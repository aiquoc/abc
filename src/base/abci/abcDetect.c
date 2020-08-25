/**CFile****************************************************************

  FileName    [abcDetect.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Detect conditions.]

  Author      [Alan Mishchenko, Dao Ai Quoc]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 7, 2016.]

  Revision    [$Id: abcDetect.c,v 1.00 2016/06/07 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/io/ioAbc.h"
#include "misc/vec/vecHsh.h"
#include "misc/util/utilNam.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "map/mio/mio.h"
#include "map/mio/exp.h"
#include "aig/gia/giaAig.h"
#include "aig/gia/gia.h"
#include "proof/fra/fra.h"
#include "proof/fraig/fraig.h"
#include "proof/cec/cec.h"


ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef enum { 
    ABC_FIN_NONE = -100,   //  0:  unknown
    ABC_FIN_SA0,           //  1:
    ABC_FIN_SA1,           //  2:
    ABC_FIN_NEG,           //  3:
    ABC_FIN_RDOB_AND,      //  4:
    ABC_FIN_RDOB_NAND,     //  5:
    ABC_FIN_RDOB_OR,       //  6:
    ABC_FIN_RDOB_NOR,      //  7:
    ABC_FIN_RDOB_XOR,      //  8:
    ABC_FIN_RDOB_NXOR,     //  9:
    ABC_FIN_RDOB_NOT,      // 10:
    ABC_FIN_RDOB_BUFF,     // 11:
    ABC_FIN_RDOB_LAST      // 12:
} Abc_FinType_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Read circuit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#define SA0 0
#define SA1 1
#define NEG 2
#define RDOB_AND 3
#define RDOB_NAND 4
#define RDOB_OR 5
#define RDOB_NOR 6
#define RDOB_XOR 7
#define RDOB_NXOR 8
#define RDOB_NOT 9
#define RDOB_BUFF 10

#define BUFF 1
#define NOT 2
#define AND 3
#define NAND 4
#define OR 5
#define NOR 6
#define XOR 7
#define NXOR 8
#define DFF 9


struct Abc_Ntk_FaultDescr {
	int id;
	unsigned  node;
	int Type;
};

struct cell {
	int input1;
	int input2;
	int input3;
	int input4;
	int output;
	int Type;
};
struct Abc_NtkCircuit {
	int *nInputs;
	int inNum;
	int *nOnputs;
	int outNum;
	struct cell *elem;
	int elemNum;
	int Type; // 0 - combinational, 1 - sequential
};
int isspace(int argument);
void trim(char * s) {
	char * p = s;
	int l = strlen(p);

	while (isspace(p[l - 1])) {
		p[--l] = 0;
		if (l == 0)
			break;
	}

	while (*p && isspace(*p)) {
		++p;
		--l;
	}

	memmove(s, p, l + 1);
}

// Read initial circuit from file
struct Abc_NtkCircuit * Abc_NtkReadInitialCircuit(char *pFileName) {
	struct Abc_NtkCircuit * pNtk;
	char buf[2048];
	char elem[16];
	int node, outNode, inNode1, inNode2, inNode3, inNode4, elemType;
	FILE *f = fopen(pFileName, "r");
	if (f == NULL) {
		printf("Couldn't open file: %s with design!", pFileName);
		exit(0);
	}
	pNtk = (struct Abc_NtkCircuit *) malloc(sizeof(struct Abc_NtkCircuit));
	pNtk->nInputs = NULL;
	pNtk->inNum = 0;
	pNtk->nOnputs = NULL;
	pNtk->outNum = 0;
	pNtk->elem = NULL;
	pNtk->elemNum = 0;
	pNtk->Type = 0;

	while (fgets(buf, 2048, f) != NULL) {
		trim(buf);
		if (strlen(buf) == 0)
			continue;
		if (buf[0] == '#')
			continue;
		// Input
		if (sscanf(buf, "INPUT(%d)", &node) == 1) {
			pNtk->nInputs = realloc(pNtk->nInputs, (pNtk->inNum + 1) * sizeof(int));
			pNtk->nInputs[pNtk->inNum] = node;
			pNtk->inNum++;
		}
		// Output
		else if (sscanf(buf, "OUTPUT(%d)", &node) == 1) {
			pNtk->nOnputs = realloc(pNtk->nOnputs, (pNtk->outNum + 1) * sizeof(int));
			pNtk->nOnputs[pNtk->outNum] = node;
			pNtk->outNum++;
		}
		// 4 input element DFF
		else if (sscanf(buf, "%d = %[^(](%d, %d, %d, %d)", &outNode, elem, &inNode1, &inNode2, &inNode3, &inNode4) == 6) {
			pNtk->elem = realloc(pNtk->elem, (pNtk->elemNum + 1) * sizeof(struct cell));
			if (!strcmp(elem, "DFF")) {
				elemType = DFF;
			}
			else {
				printf("Unknown the element: %s. Skip!\n", elem);
				continue;
			}
			pNtk->elem[pNtk->elemNum].input1 = inNode4;
			pNtk->elem[pNtk->elemNum].input2 = -1;
			pNtk->elem[pNtk->elemNum].output = outNode;
			pNtk->elem[pNtk->elemNum].Type = elemType;
			pNtk->elemNum++;
			pNtk->Type = 1; 
		}
		
		// 2 input elements
		else if (sscanf(buf, "%d = %[^(](%d, %d)", &outNode, elem, &inNode1, &inNode2) == 4) {
			pNtk->elem = realloc(pNtk->elem, (pNtk->elemNum + 1) * sizeof(struct cell));
			if (!strcmp(elem, "AND")) {
				elemType = AND;
			}
			else if (!strcmp(elem, "NAND")) {
				elemType = NAND;
			}
			else if (!strcmp(elem, "OR")) {
				elemType = OR;
			}
			else if (!strcmp(elem, "NOR")) {
				elemType = NOR;
			}
			else if (!strcmp(elem, "XOR")) {
				elemType = XOR;
			}
			else if (!strcmp(elem, "NXOR")) {
				elemType = NXOR;
			}
			else {
				printf("Unknown element: %s. Skip!\n", elem);
				continue;
			}
			pNtk->elem[pNtk->elemNum].input1 = inNode1;
			pNtk->elem[pNtk->elemNum].input2 = inNode2;
			pNtk->elem[pNtk->elemNum].output = outNode;
			pNtk->elem[pNtk->elemNum].Type = elemType;
			pNtk->elemNum++;
		}
		// 1 input element
		else if (sscanf(buf, "%d = %[^(](%d)", &outNode, elem, &inNode1) == 3) {
			pNtk->elem = realloc(pNtk->elem, (pNtk->elemNum + 1) * sizeof(struct cell));
			if (!strcmp(elem, "BUFF")) {
				elemType = BUFF;
			}
			else if (!strcmp(elem, "NOT")) {
				elemType = NOT;
			}
			else if (!strcmp(elem, "DFF")) {
				elemType = DFF;
			}
			else {
				printf("Unknown element: %s. Skip!\n", elem);
				continue;
			}
			pNtk->elem[pNtk->elemNum].input1 = inNode1;
			pNtk->elem[pNtk->elemNum].input2 = -1;
			pNtk->elem[pNtk->elemNum].output = outNode;
			pNtk->elem[pNtk->elemNum].Type = elemType;
			pNtk->elemNum++;
		}
		else {
			printf("Unknown element desciption: %s. Skip it!\n", buf);
		}

	}
	fclose(f);

	return pNtk;
}



// Create new circuit with injected faults


struct Abc_NtkCircuit * Abc_NtkInjectFault( struct Abc_NtkCircuit * pNtk, struct Abc_Ntk_FaultDescr fault, int zero_replace)
{
	int i;
	int fix_num = 0;
	int nodeType = 0;
	struct Abc_NtkCircuit * pNtkNew;

	// Alloc memory and copy initital circuit
	pNtkNew = calloc(1, sizeof(struct Abc_NtkCircuit));
	pNtkNew->inNum = pNtk->inNum;
	pNtkNew->outNum = pNtk->outNum;
	pNtkNew->elemNum = pNtk->elemNum;
	pNtkNew->nInputs = calloc(pNtkNew->inNum, sizeof(int));
	pNtkNew->nOnputs = calloc(pNtkNew->outNum, sizeof(int));
	pNtkNew->elem = calloc(pNtkNew->elemNum, sizeof(struct cell));
	for (i = 0; i < pNtkNew->inNum; i++) {
		pNtkNew->nInputs[i] = pNtk->nInputs[i];
		//printf("pNtkNew->nInputs[i]  = %d  fault.node = %d \n",pNtkNew->nInputs[i], fault.node );
		if (pNtkNew->nInputs[i] == fault.node) {
			nodeType = 1;
		}
	}
	for (i = 0; i < pNtkNew->outNum; i++) {
		pNtkNew->nOnputs[i] = pNtk->nOnputs[i];
		if (pNtkNew->nOnputs[i] == fault.node) {
			nodeType = 2;
		}
	}
	for (i = 0; i < pNtkNew->elemNum; i++) {
		pNtkNew->elem[i].input1 = pNtk->elem[i].input1;
		pNtkNew->elem[i].input2 = pNtk->elem[i].input2;
		pNtkNew->elem[i].output = pNtk->elem[i].output;
		pNtkNew->elem[i].Type = pNtk->elem[i].Type;
		if (nodeType == 0) {
			if (pNtkNew->elem[i].input1 == fault.node || pNtkNew->elem[i].input2 == fault.node || pNtkNew->elem[i].output == fault.node) {
				nodeType = 3;
			}
		}
	}

	// Check possible Faults of data
	if (nodeType == 0) {
		printf("Unknown Type for node: %d", fault.node);
		exit(0);
	}

	if (nodeType == 1 && fault.Type != SA0 && fault.Type != SA1 && fault.Type != NEG) {
		printf("Unexpected fault Type %d for input node", fault.node);
		exit(0);
	}

	// Inject fault elements
	for (i = 0; i < pNtkNew->elemNum; i++) {
		pNtkNew->elem[i].input1 = pNtk->elem[i].input1;
		pNtkNew->elem[i].input2 = pNtk->elem[i].input2;
		pNtkNew->elem[i].output = pNtk->elem[i].output;
		pNtkNew->elem[i].Type = pNtk->elem[i].Type;
		if (fault.Type == SA0 || fault.Type == SA1 || fault.Type == NEG) {
			if (pNtkNew->elem[i].input1 == fault.node) {
				if (pNtkNew->elem[i].input1 == 0) {
					pNtkNew->elem[i].input1 = -zero_replace;
				}
				else {
					pNtkNew->elem[i].input1 = -pNtkNew->elem[i].input1;
				}
				fix_num += 1;
			}
			if (pNtkNew->elem[i].input2 == fault.node) {
				if (pNtkNew->elem[i].input2 == 0) {
					pNtkNew->elem[i].input2 = -zero_replace;
				}
				else {
					pNtkNew->elem[i].input2 = -pNtkNew->elem[i].input2;
				}
				fix_num += 1;
			}
			if (nodeType == 2) {
				if (pNtkNew->elem[i].output == fault.node) {
					if (pNtkNew->elem[i].output == 0) {
						pNtkNew->elem[i].output = -zero_replace;
					}
					else {
						pNtkNew->elem[i].output = -pNtkNew->elem[i].output;
					}
					fix_num += 1;
				}
			}
		}
		else if (fault.Type == RDOB_AND && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = AND;
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NAND && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = NAND;
			fix_num += 1;
		}
		else if (fault.Type == RDOB_OR && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = OR;
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NOR && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = NOR;
			fix_num += 1;
		}
		else if (fault.Type == RDOB_XOR && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = XOR;
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NXOR && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = NXOR;
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NOT && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = NOT;
			fix_num += 1;
		}
		else if (fault.Type == RDOB_BUFF && fault.node == pNtkNew->elem[i].output) {
			pNtkNew->elem[i].Type = BUFF;
			fix_num += 1;
		}
	}

	// For some cases add additional element
	if (nodeType == 1 || nodeType == 3) {
		// Input or Internal
		if (fault.Type == SA0) {
			pNtkNew->elem = realloc(pNtkNew->elem, (pNtkNew->elemNum + 1) * sizeof(struct cell));
			pNtkNew->elem[pNtkNew->elemNum].input1 = fault.node;
			pNtkNew->elem[pNtkNew->elemNum].input2 = fault.node;
			if (fault.node == 0) {
				pNtkNew->elem[pNtkNew->elemNum].output = -zero_replace;
			}
			else {
				pNtkNew->elem[pNtkNew->elemNum].output = -fault.node;
			}
			pNtkNew->elem[pNtkNew->elemNum].Type = XOR;
			pNtkNew->elemNum += 1;
		}
		else if (fault.Type == SA1) {
			pNtkNew->elem = realloc(pNtkNew->elem, (pNtkNew->elemNum + 1) * sizeof(struct cell));
			pNtkNew->elem[pNtkNew->elemNum].input1 = fault.node;
			pNtkNew->elem[pNtkNew->elemNum].input2 = fault.node;
			if (fault.node == 0) {
				pNtkNew->elem[pNtkNew->elemNum].output = -zero_replace;
			} 
			else {
				pNtkNew->elem[pNtkNew->elemNum].output = -fault.node;
			}
			pNtkNew->elem[pNtkNew->elemNum].Type = NXOR;
			pNtkNew->elemNum += 1;
		}
		else if (fault.Type == NEG) {
			pNtkNew->elem = realloc(pNtkNew->elem, (pNtkNew->elemNum + 1) * sizeof(struct cell));
			pNtkNew->elem[pNtkNew->elemNum].input1 = fault.node;
			if (fault.node == 0) {
				pNtkNew->elem[pNtkNew->elemNum].output = -zero_replace;
			}
			else {
				pNtkNew->elem[pNtkNew->elemNum].output = -fault.node;
			}
			pNtkNew->elem[pNtkNew->elemNum].Type = NOT;
			pNtkNew->elemNum += 1;
		}
	}
	else if (nodeType == 2) {
		// Output
		if (fault.Type == SA0) {
			pNtkNew->elem = realloc(pNtkNew->elem, (pNtkNew->elemNum + 1) * sizeof(struct cell));
			if (fault.node == 0) {
				pNtkNew->elem[pNtkNew->elemNum].input1 = -zero_replace;
				pNtkNew->elem[pNtkNew->elemNum].input2 = -zero_replace;
			}
			else {
				pNtkNew->elem[pNtkNew->elemNum].input1 = -fault.node;
				pNtkNew->elem[pNtkNew->elemNum].input2 = -fault.node;
			}
			pNtkNew->elem[pNtkNew->elemNum].output = fault.node;
			pNtkNew->elem[pNtkNew->elemNum].Type = XOR;
			pNtkNew->elemNum += 1;
		}
		else if (fault.Type == SA1) {
			pNtkNew->elem = realloc(pNtkNew->elem, (pNtkNew->elemNum + 1) * sizeof(struct cell));
			if (fault.node == 0) {
				pNtkNew->elem[pNtkNew->elemNum].input1 = -zero_replace;
				pNtkNew->elem[pNtkNew->elemNum].input2 = -zero_replace;
			}
			else {
				pNtkNew->elem[pNtkNew->elemNum].input1 = -fault.node;
				pNtkNew->elem[pNtkNew->elemNum].input2 = -fault.node;
			}
			pNtkNew->elem[pNtkNew->elemNum].output = fault.node;
			pNtkNew->elem[pNtkNew->elemNum].Type = NXOR;
			pNtkNew->elemNum += 1;
		}
		else if (fault.Type == NEG) {
			pNtkNew->elem = realloc(pNtkNew->elem, (pNtkNew->elemNum + 1) * sizeof(struct cell));
			if (fault.node == 0) {
				pNtkNew->elem[pNtkNew->elemNum].input1 = -zero_replace;
			}
			else {
				pNtkNew->elem[pNtkNew->elemNum].input1 = -fault.node;
			}
			pNtkNew->elem[pNtkNew->elemNum].output = fault.node;
			pNtkNew->elem[pNtkNew->elemNum].Type = NOT;
			pNtkNew->elemNum += 1;
		}
	}
	
	return pNtkNew;
}

void Abc_NtkFreeCircuit(struct Abc_NtkCircuit * pNtk) {
	free(pNtk->nInputs);
	free(pNtk->nOnputs);
	free(pNtk->elem);
}

// function to convert circuit into Abc_Ntk_t format
Abc_Ntk_t * Abc_CirtoNtk(struct Abc_NtkCircuit * p)
{

	Abc_Ntk_t * pNtk;
	Abc_Obj_t * pNode;
	char inname[10], outname[10], in1[10], in2[10], out[10];
	int i, Type;

	// allocate the empty network
	pNtk = Abc_NtkStartRead("temp");

	// go through nInputs

	for (i = 0; i < p->inNum; i++)
	{
		snprintf(inname, sizeof(inname), "%d", p->nInputs[i]);
		Io_ReadCreatePi(pNtk, inname); 
	}
	
	for (i = 0; i < p->outNum; i++)
	{
		snprintf(outname, sizeof(outname), "%d", p->nOnputs[i]);
		Io_ReadCreatePo(pNtk, outname); 
	}

	for (i = 0; i < p->elemNum; i++)
	{
		Type = p->elem[i].Type;
		snprintf(in1, sizeof(in1), "%d", p->elem[i].input1);
		snprintf(in2, sizeof(in2), "%d", p->elem[i].input2);
		snprintf(out, sizeof(out), "%d", p->elem[i].output);
		char *nInputs[] = { in1, in2 };

		if (Type == 9)
		{
			pNode = Io_ReadCreateLatch(pNtk, in1, out); //  DFF
			Abc_LatchSetInit0(pNode);
		}
		else if (Type == 1)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 1);
			Abc_ObjSetData(pNode, Abc_SopCreateBuf((Mem_Flex_t *)pNtk->pManFunc));
																				 
		}
		else if (Type == 2)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 1);
			Abc_ObjSetData(pNode, Abc_SopCreateInv((Mem_Flex_t *)pNtk->pManFunc)); 
																				   
		}
		else if (Type == 3)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 2);
			Abc_ObjSetData(pNode, Abc_SopCreateAnd((Mem_Flex_t *)pNtk->pManFunc, 2, NULL)); 
																							
		}
		else if (Type == 4)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 2);
			Abc_ObjSetData(pNode, Abc_SopCreateNand((Mem_Flex_t *)pNtk->pManFunc, 2)); 
																					   
		}
		else if (Type == 5)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 2);
			Abc_ObjSetData(pNode, Abc_SopCreateOr((Mem_Flex_t *)pNtk->pManFunc, 2, NULL));
																						   
		}
		else if (Type == 6)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 2);
			Abc_ObjSetData(pNode, Abc_SopCreateNor((Mem_Flex_t *)pNtk->pManFunc, 2)); 
																					  
		}
		else if (Type == 7)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 2);
			Abc_ObjSetData(pNode, Abc_SopCreateXor((Mem_Flex_t *)pNtk->pManFunc, 2)); 
																					 
		}
		else if (Type == 8)
		{
			pNode = Io_ReadCreateNode(pNtk, out, nInputs, 2);
			Abc_ObjSetData(pNode, Abc_SopCreateNxor((Mem_Flex_t *)pNtk->pManFunc, 2)); 
																					   
		}
		else
		{
			printf("Io_ReadBenchNetwork(): Cannot determine gate Type \"%d\" in line .\n", Type);
			Abc_NtkDelete(pNtk);
			return NULL;
		}

	}

	Abc_NtkFinalizeRead(pNtk);
	return pNtk;
}

Abc_Ntk_t ** Abc_NtkGenerateAllCircuitsArray(struct Abc_NtkCircuit ** pNtk, int nFaultNum) {
	int i;
	Abc_Ntk_t **pNtk_array;

	pNtk_array = (Abc_Ntk_t**) malloc(nFaultNum * sizeof(Abc_Ntk_t *));
	for (i = 0; i < nFaultNum; i++)
	{
		Abc_Ntk_t *bench, *logic;
		
			bench = Abc_CirtoNtk(pNtk[i]);	
			logic = Abc_NtkToLogic(bench);
			pNtk_array[i] = Abc_NtkStrash(logic, 1, 1, 1);		
			Abc_NtkDelete(bench);
			Abc_NtkDelete(logic);	
	}
	return pNtk_array;
}
void Abc_NtkFreeCircuits(Abc_Ntk_t ** fNtk, int nFaultNum) {
	int i;
	for (i = 0; i < nFaultNum; i++) {
		Abc_NtkDelete(fNtk[i]);
	}
	free(fNtk);
	return;
}
Abc_Ntk_t * Abc_ReadCircuit( char * pFileName, int fVerbose )
{
	struct Abc_NtkCircuit * pNktcirc = NULL;
	Abc_Ntk_t * pNtk, * pNewNtk = NULL;
	pNktcirc = Abc_NtkReadInitialCircuit(pFileName);
	pNtk = Abc_CirtoNtk(pNktcirc);
	pNewNtk = Abc_NtkToLogic(pNtk);
	Abc_NtkDelete(pNtk);
	Abc_NtkFreeCircuit(pNktcirc);
	return pNewNtk;
}

int Abc_NtkDesignType(char *pFileNames) {
	int i, len;
	char buf[2048];
	FILE *f = fopen(pFileNames, "r");
	if (f == NULL) {
		printf("Couldn't open file: %s with design!", pFileNames);
		exit(0);
	}

	while (fgets(buf, 2048, f) != NULL) {
		len = strlen(buf);
		if (len < 3)
			continue;
		for (i = 0; i < len - 3; i++) {
			if (buf[i] == 'D' && buf[i + 1] == 'F' && buf[i + 2] == 'F') {
				fclose(f);
				return 1;
			}
		}
	}
	fclose(f);
	return 0;
}

/**Function*************************************************************

  Synopsis    [Generates fault list for the given mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkReadFaultInf(char *pFileName, struct Abc_Ntk_FaultDescr **faults, int *fault_num) {
	struct Abc_Ntk_FaultDescr *fl = NULL;
	int nFaultNum = 0;
	int id, node;
	char buf[2048];
	FILE *f = fopen(pFileName, "r");
	if (f == NULL) {
		printf("Cannot open file: %s with faults!", pFileName);
		exit(0);
	}

	while (fscanf(f, "%d %d %s", &id, &node, buf) != EOF) {
		fl = realloc(fl, (nFaultNum + 1) * sizeof(struct Abc_Ntk_FaultDescr));
		fl[nFaultNum].id = id;
		fl[nFaultNum].node = node;
		if (!strcmp(buf, "SA0")) {
			fl[nFaultNum].Type = SA0;
		}
		else if (!strcmp(buf, "SA1")) {
			fl[nFaultNum].Type = SA1;
		}
		else if (!strcmp(buf, "NEG")) {
			fl[nFaultNum].Type = NEG;
		}
		else if (!strcmp(buf, "RDOB_AND")) {
			fl[nFaultNum].Type = RDOB_AND;
		}
		else if (!strcmp(buf, "RDOB_NAND")) {
			fl[nFaultNum].Type = RDOB_NAND;
		}
		else if (!strcmp(buf, "RDOB_OR")) {
			fl[nFaultNum].Type = RDOB_OR;
		}
		else if (!strcmp(buf, "RDOB_NOR")) {
			fl[nFaultNum].Type = RDOB_NOR;
		}
		else if (!strcmp(buf, "RDOB_XOR")) {
			fl[nFaultNum].Type = RDOB_XOR;
		}
		else if (!strcmp(buf, "RDOB_NXOR")) {
			fl[nFaultNum].Type = RDOB_NXOR;
		}
		else if (!strcmp(buf, "RDOB_NOT")) {
			fl[nFaultNum].Type = RDOB_NOT;
		}
		else if (!strcmp(buf, "RDOB_BUFF")) {
			fl[nFaultNum].Type = RDOB_BUFF;
		}
		else {
			printf("Unknown Type %s in fault description!", buf);
			exit(0);
		}
		nFaultNum++;
	}
	*fault_num = nFaultNum;
	*faults = fl;
	fclose(f);
}

void Abc_NtkGenFaultList( Abc_Ntk_t * pNtk, char * pFileName )
{
    Mio_Library_t * pLib = (Mio_Library_t *)pNtk->pManFunc;
    Mio_Gate_t * pGate;
    Abc_Obj_t * pObj;
    int i, Count = 1;
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        return;
    }
    assert( Abc_NtkIsMappedLogic(pNtk) );
	Abc_NtkForEachPi(pNtk, pObj,i){
		//Mio_Gate_t * pGateObj = (Mio_Gate_t *)pObj->pData;
		 fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "SA0" ), Count++;
        fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "SA1" ), Count++;
		  fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "NEG" ), Count++;
		  
	}
	Abc_NtkForEachPo(pNtk, pObj,i){
		//Mio_Gate_t * pGateObj = (Mio_Gate_t *)pObj->pData;
		 fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "SA0" ), Count++;
        fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "SA1" ), Count++;
		  fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "NEG" ), Count++;
	}
	Abc_NtkForEachNode( pNtk, pObj, i )
    {
        
		Mio_Gate_t * pGateObj = (Mio_Gate_t *)pObj->pData;
        int nInputs = Mio_GateReadPinNum(pGateObj);
        // add basic faults (SA0, SA1, NEG)
        fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "SA0" ), Count++;
        fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "SA1" ), Count++;
       fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), "NEG" ), Count++;
        // add other faults, which correspond to changing the given gate
        // by another gate with the same support-size from the same library
       Mio_LibraryForEachGate( pLib, pGate )
           if ( pGate != pGateObj && Mio_GateReadPinNum(pGate) == nInputs )
              fprintf( pFile, "%d %s %s\n", Count, Abc_ObjName(pObj), Mio_GateReadName(pGate) ), Count++;
    }
  
    printf( "Generated fault list \"%s\" for network \"%s\" with %d nodes and %d faults.\n", 
        pFileName, Abc_NtkName(pNtk), Abc_NtkNodeNum(pNtk), Count-1 );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Recognize Type.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadFinTypeMapped( Mio_Library_t * pLib, char * pThis )
{
    Mio_Gate_t * pGate = Mio_LibraryReadGateByName( pLib, pThis, NULL );
    if ( pGate == NULL )
    {
        printf( "Cannot find gate \"%s\" in the current library.\n", pThis );
        return ABC_FIN_NONE;
    }
    return Mio_GateReadCell( pGate );
}
int Io_ReadFinType( char * pThis )
{
    if ( !strcmp(pThis, "SA0") )        return ABC_FIN_SA0;
    if ( !strcmp(pThis, "SA1") )        return ABC_FIN_SA1;
    if ( !strcmp(pThis, "NEG") )        return ABC_FIN_NEG;
    if ( !strcmp(pThis, "RDOB_AND") )   return ABC_FIN_RDOB_AND;
    if ( !strcmp(pThis, "RDOB_NAND") )  return ABC_FIN_RDOB_NAND;
    if ( !strcmp(pThis, "RDOB_OR") )    return ABC_FIN_RDOB_OR;
    if ( !strcmp(pThis, "RDOB_NOR") )   return ABC_FIN_RDOB_NOR;
    if ( !strcmp(pThis, "RDOB_XOR") )   return ABC_FIN_RDOB_XOR;
    if ( !strcmp(pThis, "RDOB_NXOR") )  return ABC_FIN_RDOB_NXOR;
    if ( !strcmp(pThis, "RDOB_NOT") )   return ABC_FIN_RDOB_NOT;
    if ( !strcmp(pThis, "RDOB_BUFF") )  return ABC_FIN_RDOB_BUFF;
    return ABC_FIN_NONE;
}
char * Io_WriteFinType( int Type )
{
    if ( Type == ABC_FIN_SA0 )          return "SA0";
    if ( Type == ABC_FIN_SA1 )          return "SA1";
    if ( Type == ABC_FIN_NEG )          return "NEG";
    if ( Type == ABC_FIN_RDOB_AND  )    return "RDOB_AND" ;
    if ( Type == ABC_FIN_RDOB_NAND )    return "RDOB_NAND";
    if ( Type == ABC_FIN_RDOB_OR   )    return "RDOB_OR"  ;
    if ( Type == ABC_FIN_RDOB_NOR  )    return "RDOB_NOR" ;
    if ( Type == ABC_FIN_RDOB_XOR  )    return "RDOB_XOR" ;
    if ( Type == ABC_FIN_RDOB_NXOR )    return "RDOB_NXOR";
    if ( Type == ABC_FIN_RDOB_NOT  )    return "RDOB_NOT" ;
    if ( Type == ABC_FIN_RDOB_BUFF )    return "RDOB_BUFF";
    return "Unknown";
}

/**Function*************************************************************

  Synopsis    [Read information from file.]

  Description [Returns information as a set of pairs: (ObjId, TypeId).
  Uses the current network to map ObjName given in the file into ObjId.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Io_ReadFins( Abc_Ntk_t * pNtk, char * pFileName, int fVerbose )
{
    Mio_Library_t * pLib = (Mio_Library_t *)pNtk->pManFunc;
    char Buffer[1000];
    Abc_Obj_t * pObj;
    Abc_Nam_t * pNam;
    Vec_Int_t * vMap; 
    Vec_Int_t * vPairs = NULL;
    int i, Type, iObj, fFound, nLines = 1;
    FILE * pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Cannot open input file \"%s\" for reading.\n", pFileName );
        return NULL;
    }
    // map CI/node names into their IDs
    pNam = Abc_NamStart( 1000, 10 );
    vMap = Vec_IntAlloc( 1000 );
    Vec_IntPush( vMap, -1 );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsCi(pObj) && !Abc_ObjIsNode(pObj) )
            continue;
        Abc_NamStrFindOrAdd( pNam, Abc_ObjName(pObj), &fFound );
        //if ( fFound )
        //{
          //  printf( "The same name \"%s\" appears twice among CIs and internal nodes.\n", Abc_ObjName(pObj) );
           // goto finish;
        //}
        Vec_IntPush( vMap, Abc_ObjId(pObj) );
    }
    //assert( Vec_IntSize(vMap) == Abc_NamObjNumMax(pNam) );
    // read file lines
    vPairs = Vec_IntAlloc( 1000 );
    Vec_IntPushTwo( vPairs, -1, -1 );
    while ( fgets(Buffer, 1000, pFile) != NULL )
    {
        // read line number
        char * pToken = strtok( Buffer, " \n\r\t" );
        if ( pToken == NULL )
            break;
        if ( nLines++ != atoi(pToken) )
        {
            printf( "Line numbers are not consecutive. Quitting.\n" );
            Vec_IntFreeP( &vPairs );
            goto finish;
        }
        // read object name and find its ID
        pToken = strtok( NULL, " \n\r\t" );
        iObj = Abc_NamStrFind( pNam, pToken );
        if ( !iObj )
        {
            printf( "Cannot find object with name \"%s\".\n", pToken );
            continue;
        }
        // read Type
        pToken = strtok( NULL, " \n\r\t" );
        if ( Abc_NtkIsMappedLogic(pNtk) )
        {
            if ( !strcmp(pToken, "SA0") || !strcmp(pToken, "SA1") || !strcmp(pToken, "NEG") )
                Type = Io_ReadFinType( pToken );
            else
                Type = Io_ReadFinTypeMapped( pLib, pToken );
        }
        else
            Type = Io_ReadFinType( pToken );
        if ( Type == ABC_FIN_NONE )
        {
            printf( "Cannot read Type \"%s\" of object \"%s\".\n", pToken, Abc_ObjName(Abc_NtkObj(pNtk, iObj)) );
            continue;
        }
        Vec_IntPushTwo( vPairs, Vec_IntEntry(vMap, iObj), Type );
    }
    assert( Vec_IntSize(vPairs) == 2 * nLines );
    printf( "Finished reading %d lines from the fault list file \"%s\".\n", nLines - 1, pFileName );

    // verify the reader by printing the results
    if ( fVerbose )
        Vec_IntForEachEntryDoubleStart( vPairs, iObj, Type, i, 2 )
            printf( "%-10d%-10s%-10s\n", i/2, Abc_ObjName(Abc_NtkObj(pNtk, iObj)), Io_WriteFinType(Type) );

finish:
    Vec_IntFree( vMap );
    Abc_NamDeref( pNam );
    fclose( pFile );
    return vPairs;
}


int Abc_NtkEquivDsec(Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2)
{
	extern int Abc_NtkDarSec(Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Fra_Sec_t * p);
	Fra_Sec_t SecPar, *pSecPar = &SecPar;

	// set defaults
	Fra_SecSetDefaultParams(pSecPar);
	pSecPar->TimeLimit = 0;
	pSecPar->fSilent = 1;
	// perform verification

	return Abc_NtkDarSec(pNtk1, pNtk2, pSecPar);;

}


/**Function*************************************************************

  Synopsis    [Extend the network by adding second timeframe.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFrameExtend( Abc_Ntk_t * pNtk )
{
    
	Vec_Ptr_t * vFanins, * vNodes;
    Abc_Obj_t * pObj, * pFanin, * pReset, * pEnable, * pSignal;
    Abc_Obj_t * pResetN, * pEnableN, * pAnd0, * pAnd1, * pMux;
    int i, k, iStartPo, nPisOld = Abc_NtkPiNum(pNtk), nPosOld = Abc_NtkPoNum(pNtk);
		
    // skip if there are no flops
    if ( pNtk->nConstrs == 0 )
        return;
    assert( Abc_NtkPiNum(pNtk) >= pNtk->nConstrs );
    assert( Abc_NtkPoNum(pNtk) >= pNtk->nConstrs * 4 );
	
    // collect nodes
    vNodes = Vec_PtrAlloc( Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
        Vec_PtrPush( vNodes, pObj );
    // duplicate PIs
    vFanins = Vec_PtrAlloc( 2 );
	int f;
	int nFrames = 50;
	for (f = 0; f < nFrames; f++){
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        if ( i == nPisOld )
            break;
        if ( i < nPisOld - pNtk->nConstrs )
        {
            Abc_NtkDupObj( pNtk, pObj, 0 );
            Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(pObj), "_frame1" );
            continue;
        }
		
        // create flop input
        iStartPo = nPosOld + 4 * (i - nPisOld);
		
        pReset   = Abc_ObjFanin0( Abc_NtkPo( pNtk, iStartPo + 1 ) );
        pEnable  = Abc_ObjFanin0( Abc_NtkPo( pNtk, iStartPo + 2 ) );
        pSignal  = Abc_ObjFanin0( Abc_NtkPo( pNtk, iStartPo + 3 ) );
        pResetN  = Abc_NtkCreateNodeInv( pNtk, pReset );
        pEnableN = Abc_NtkCreateNodeInv( pNtk, pEnable );
        Vec_PtrFillTwo( vFanins, 2, pEnableN, pObj );
        pAnd0    = Abc_NtkCreateNodeAnd( pNtk, vFanins );
        Vec_PtrFillTwo( vFanins, 2, pEnable, pSignal );
        pAnd1    = Abc_NtkCreateNodeAnd( pNtk, vFanins );
        Vec_PtrFillTwo( vFanins, 2, pAnd0, pAnd1 );
        pMux     = Abc_NtkCreateNodeOr( pNtk, vFanins );
        Vec_PtrFillTwo( vFanins, 2, pResetN, pMux );
		pObj->pCopy = Abc_NtkCreateNodeAnd( pNtk, vFanins );
		
    }
    // duplicate internal nodes
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        Abc_NtkDupObj( pNtk, pObj, 0 );
    // connect objects
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );	
    // create new POs and reconnect flop inputs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        if ( i == nPosOld )
            break;
        if ( i < nPosOld - 4 * pNtk->nConstrs )
        {
            Abc_NtkDupObj( pNtk, pObj, 0 );
            Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(pObj), "_frame1" );
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pObj)->pCopy );

			continue;
        }
        Abc_ObjPatchFanin( pObj, Abc_ObjFanin0(pObj), Abc_ObjFanin0(pObj)->pCopy );
		
    }
	}
    Vec_PtrFree( vFanins );
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    [Detect equivalence classes of nodes in terms of their TFO.]

  Description [Given is the logic network (pNtk) and the set of objects
  (primary inputs or internal nodes) to be considered (vObjs), this function
  returns a set of equivalence classes of these objects in terms of their 
  transitive fanout (TFO). Two objects belong to the same class if the set 
  of COs they feed into are the same.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDetectObjClasses_rec( Abc_Obj_t * pObj, Vec_Int_t * vMap, Hsh_VecMan_t * pHash, Vec_Int_t * vTemp )
{
    Vec_Int_t * vArray, * vSet;
    Abc_Obj_t * pNext; int i;
    // get the CO set for this object
    int Entry = Vec_IntEntry(vMap, Abc_ObjId(pObj));
	
    if ( Entry != -1 ) // the set is already computed
        return Entry;
    // compute a new CO set
    assert( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) );
    // if there is no fanouts, the set of COs is empty
    if ( Abc_ObjFanoutNum(pObj) == 0 )
    {
        Vec_IntWriteEntry( vMap, Abc_ObjId(pObj), 0 );
        return 0;
    }
    // compute the set for the first fanout
    Entry = Abc_NtkDetectObjClasses_rec( Abc_ObjFanout0(pObj), vMap, pHash, vTemp );
    if ( Abc_ObjFanoutNum(pObj) == 1 )
    {
        Vec_IntWriteEntry( vMap, Abc_ObjId(pObj), Entry );
        return Entry;
    }
    vSet = Vec_IntAlloc( 16 );
    // initialize the set with that of first fanout
    vArray = Hsh_VecReadEntry( pHash, Entry );
    Vec_IntClear( vSet );
    Vec_IntAppend( vSet, vArray );
    // iteratively add sets of other fanouts
    Abc_ObjForEachFanout( pObj, pNext, i )
    {
        if ( i == 0 ) 
            continue;
        Entry = Abc_NtkDetectObjClasses_rec( pNext, vMap, pHash, vTemp );
        vArray = Hsh_VecReadEntry( pHash, Entry );
        Vec_IntTwoMerge2( vSet, vArray, vTemp );
        ABC_SWAP( Vec_Int_t, *vSet, *vTemp );
    }
    // create or find new set and map the object into it
    Entry = Hsh_VecManAdd( pHash, vSet );
    Vec_IntWriteEntry( vMap, Abc_ObjId(pObj), Entry );
    Vec_IntFree( vSet );
    return Entry;
}
Vec_Wec_t * Abc_NtkDetectObjClasses( Abc_Ntk_t * pNtk, Vec_Int_t * vObjs, Vec_Wec_t ** pvCos )
{
    Vec_Wec_t * vClasses;   // classes of equivalence objects from vObjs
    Vec_Int_t * vClassMap;  // mapping of each CO set into its class in vClasses
    Vec_Int_t * vClass;     // one equivalence class     
    Abc_Obj_t * pObj; 
    int i, iObj, SetId, ClassId;
    // create hash table to hash sets of CO indexes
    Hsh_VecMan_t * pHash = Hsh_VecManStart( 1000 );
    // create elementary sets (each composed of one CO) and map COs into them
    Vec_Int_t * vMap = Vec_IntStartFull( Abc_NtkObjNumMax(pNtk) );
    Vec_Int_t * vSet = Vec_IntAlloc( 16 );
    assert( Abc_NtkIsLogic(pNtk) );
    // compute empty set
    SetId = Hsh_VecManAdd( pHash, vSet );
    assert( SetId == 0 );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
		Vec_IntFill( vSet, 1, Abc_ObjId(pObj) );
        SetId = Hsh_VecManAdd( pHash, vSet );
        Vec_IntWriteEntry( vMap, Abc_ObjId(pObj), SetId );//vMap vector of IDs
    }
    // make sure the array of objects is sorted
    Vec_IntSort( vObjs, 0 );

    // begin from the objects and map their IDs into sets of COs

    Abc_NtkForEachObjVec( vObjs, pNtk, pObj, i ){
        Abc_NtkDetectObjClasses_rec( pObj, vMap, pHash, vSet );
	}
		
    Vec_IntFree( vSet );
    // create map for mapping CO set its their classes
    vClassMap = Vec_IntStartFull( Hsh_VecSize(pHash) + 1 );
    // collect classes of objects
    vClasses = Vec_WecAlloc( 1000 );
    Vec_IntForEachEntry( vObjs, iObj, i )
    {
       
		//char * pName = Abc_ObjName( Abc_NtkObj(pNtk, iObj) );
        // for a given object (iObj), find the ID of its COs set
		SetId = Vec_IntEntry( vMap, iObj );	
        assert( SetId >= 0 );
        // for the given CO set, finds its equivalence class
        ClassId = Vec_IntEntry( vClassMap, SetId );	

        if ( ClassId == -1 )  // there is no equivalence class
        {
            // map this CO set into a new equivalence class
            Vec_IntWriteEntry( vClassMap, SetId, Vec_WecSize(vClasses) );
            vClass = Vec_WecPushLevel( vClasses );
        }
        else // get hold of the equivalence class
            vClass = Vec_WecEntry( vClasses, ClassId );
        // add objects to the class
        Vec_IntPush( vClass, iObj );
       //  print the set for this object
       // printf( "Object %5d : ", iObj );
      //  Vec_IntPrint( Hsh_VecReadEntry(pHash, SetId) );
    }
    // collect arrays of COs for each class
    *pvCos = Vec_WecStart( Vec_WecSize(vClasses) );
    Vec_WecForEachLevel( vClasses, vClass, i )
    {
        iObj = Vec_IntEntry( vClass, 0 );
        // for a given object (iObj), find the ID of its COs set
        SetId = Vec_IntEntry( vMap, iObj );
        assert( SetId >= 0 );
        // for the given CO set ID, find the set
        vSet = Hsh_VecReadEntry( pHash, SetId );
        Vec_IntAppend( Vec_WecEntry(*pvCos, i), vSet );
    }
    Hsh_VecManStop( pHash );
    Vec_IntFree( vClassMap );
    Vec_IntFree( vMap );
	//Vec_WecPrint(vClasses, 0);
    return vClasses;
}
void Abc_NtkDetectClassesTest2( Abc_Ntk_t * pNtk, int fVerbose, int fVeryVerbose )
{
    Vec_Int_t * vObjs;
    Vec_Wec_t * vRes, * vCos;
    // for testing, create the set of object IDs for all combinational inputs (CIs)
    Abc_Obj_t * pObj; int i;
    vObjs = Vec_IntAlloc( Abc_NtkCiNum(pNtk) );
    Abc_NtkForEachCi( pNtk, pObj, i )
        Vec_IntPush( vObjs, Abc_ObjId(pObj) );
    // compute equivalence classes of CIs and print them
    vRes = Abc_NtkDetectObjClasses( pNtk, vObjs, &vCos );
    Vec_WecPrint( vRes, 0 );
    Vec_WecPrint( vCos, 0 );
    // clean up
    Vec_IntFree( vObjs );
    Vec_WecFree( vRes );
    Vec_WecFree( vCos );
}

/**Function*************************************************************

  Synopsis    [Collecting objects.]

  Description [Collects combinational inputs (vCIs) and internal nodes (vNodes)
  reachable from the given set of combinational outputs (vCOs).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFinMiterCollect_rec( Abc_Obj_t * pObj, Vec_Int_t * vCis, Vec_Int_t * vNodes )
{
   // printf("%d %d \n", Abc_ObjId(pObj), Abc_NodeIsTravIdCurrent(pObj));
   
	if ( Abc_NodeIsTravIdCurrent(pObj) )
        return;
    Abc_NodeSetTravIdCurrent(pObj);
	//Vec_IntPrint(&Abc_ObjNtk(pObj)->vTravIds);
    if ( Abc_ObjIsCi(pObj) )
		Vec_IntPush( vCis, Abc_ObjId(pObj) );
    else
    {
        Abc_Obj_t * pFanin; int i;
        assert( Abc_ObjIsNode( pObj ) );
        Abc_ObjForEachFanin( pObj, pFanin, i )
            Abc_NtkFinMiterCollect_rec( pFanin, vCis, vNodes );
        Vec_IntPush( vNodes, Abc_ObjId(pObj) );
    }
}
void Abc_NtkFinMiterCollect( Abc_Ntk_t * pNtk, Vec_Int_t * vCos, Vec_Int_t * vCis, Vec_Int_t * vNodes )
{
    Abc_Obj_t * pObj; int i;
    Vec_IntClear( vCis );
    Vec_IntClear( vNodes );
    Abc_NtkIncrementTravId( pNtk );
	
	//Vec_IntPrint(&pNtk->vTravIds);
    Abc_NtkForEachObjVec( vCos, pNtk, pObj, i ){
		//Vec_IntPrint(vCos);
        Abc_NtkFinMiterCollect_rec( Abc_ObjFanin0(pObj), vCis, vNodes );
	}
}



/**Function*************************************************************

  Synopsis    [Simulates expression using given simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_LibGateSimulate( Mio_Gate_t * pGate, word * ppFaninSims[6], int nWords, word * pObjSim )
{
    int i, w, nVars = Mio_GateReadPinNum(pGate);
    Vec_Int_t * vExpr = Mio_GateReadExpr( pGate );
    assert( nVars <= 6 );
    for ( w = 0; w < nWords; w++ )
    {
        word uFanins[6];
        for ( i = 0; i < nVars; i++ )
            uFanins[i] = ppFaninSims[i][w];
        pObjSim[w] = Exp_Truth6( nVars, vExpr, uFanins );
    }
}

/**Function*************************************************************

  Synopsis    [Simulates expression for one simulation pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mio_LibGateSimulateOne( Mio_Gate_t * pGate, int iBits[6] )
{
    int nVars = Mio_GateReadPinNum(pGate);
    int i, iMint = 0;
    for ( i = 0; i < nVars; i++ )
        if ( iBits[i] )
            iMint |= (1 << i);
    return Abc_InfoHasBit( (unsigned *)Mio_GateReadTruthP(pGate), iMint );
}

/**Function*************************************************************

  Synopsis    [Simulated expression with one bit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mio_LibGateSimulateGia( Gia_Man_t * pGia, Mio_Gate_t * pGate, int iLits[6], Vec_Int_t * vLits )
{
    int i, nVars = Mio_GateReadPinNum(pGate);
    Vec_Int_t * vExpr = Mio_GateReadExpr( pGate );
    if ( Exp_IsConst0(vExpr) )
        return 0;
    if ( Exp_IsConst1(vExpr) )
        return 1;
    if ( Exp_IsLit(vExpr) )
    {
        int Index0  = Vec_IntEntry(vExpr,0) >> 1;
        int fCompl0 = Vec_IntEntry(vExpr,0) & 1;
        assert( Index0 < nVars );
        return Abc_LitNotCond( iLits[Index0], fCompl0 );
    }
    Vec_IntClear( vLits );
    for ( i = 0; i < nVars; i++ )
        Vec_IntPush( vLits, iLits[i] );
    for ( i = 0; i < Exp_NodeNum(vExpr); i++ )
    {
        int Index0  = Vec_IntEntry( vExpr, 2*i+0 ) >> 1;
        int Index1  = Vec_IntEntry( vExpr, 2*i+1 ) >> 1;
        int fCompl0 = Vec_IntEntry( vExpr, 2*i+0 ) & 1;
        int fCompl1 = Vec_IntEntry( vExpr, 2*i+1 ) & 1;
        Vec_IntPush( vLits, Gia_ManHashAnd( pGia, Abc_LitNotCond(Vec_IntEntry(vLits, Index0), fCompl0), Abc_LitNotCond(Vec_IntEntry(vLits, Index1), fCompl1) ) );
    }
    return Abc_LitNotCond( Vec_IntEntryLast(vLits), Vec_IntEntryLast(vExpr) & 1 );
}

/**Function*************************************************************

  Synopsis    [AIG construction and simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_NtkFinSimOneLit( Gia_Man_t * pNew, Abc_Obj_t * pObj, int Type, Vec_Int_t * vMap, int n, Vec_Int_t * vTemp )
{
    if ( Abc_NtkIsMappedLogic(pObj->pNtk) && Type >= 0 )
    {
        extern int Mio_LibGateSimulateGia( Gia_Man_t * pGia, Mio_Gate_t * pGate, int iLits[6], Vec_Int_t * vLits );
        Mio_Library_t * pLib = (Mio_Library_t *)pObj->pNtk->pManFunc;
        int i, Lits[6];
        for ( i = 0; i < Abc_ObjFaninNum(pObj); i++ )
            Lits[i] = Vec_IntEntry( vMap, Abc_Var2Lit(Abc_ObjFaninId(pObj, i), n) );
        return Mio_LibGateSimulateGia( pNew, Mio_LibraryReadGateById(pLib, Type), Lits, vTemp );
    }
    else
    {
		int iLit0 = Abc_ObjFaninNum(pObj) > 0 ? Vec_IntEntry( vMap, Abc_Var2Lit(Abc_ObjFaninId0(pObj), n) ) : -1;
        int iLit1 = Abc_ObjFaninNum(pObj) > 1 ? Vec_IntEntry( vMap, Abc_Var2Lit(Abc_ObjFaninId1(pObj), n) ) : -1;	
        assert( Type != ABC_FIN_NEG );
        if ( Type == ABC_FIN_SA0 )            return 0;
        if ( Type == ABC_FIN_SA1 )            return 1;
        if ( Type == ABC_FIN_RDOB_BUFF )      return iLit0;
        if ( Type == ABC_FIN_RDOB_NOT )       return Abc_LitNot( iLit0 );
        if ( Type == ABC_FIN_RDOB_AND )       return Gia_ManHashAnd( pNew, iLit0, iLit1 );
        if ( Type == ABC_FIN_RDOB_OR )        return Gia_ManHashOr( pNew, iLit0, iLit1 );
        if ( Type == ABC_FIN_RDOB_XOR )       return Gia_ManHashXor( pNew, iLit0, iLit1 );
        if ( Type == ABC_FIN_RDOB_NAND )      return Abc_LitNot(Gia_ManHashAnd( pNew, iLit0, iLit1 ));
        if ( Type == ABC_FIN_RDOB_NOR )       return Abc_LitNot(Gia_ManHashOr( pNew, iLit0, iLit1 ));
        if ( Type == ABC_FIN_RDOB_NXOR )      return Abc_LitNot(Gia_ManHashXor( pNew, iLit0, iLit1 ));
        assert( 0 );
        return -1;
    }
}
static inline int Abc_NtkFinSimOneBit( Abc_Obj_t * pObj, int Type, Vec_Wrd_t * vSims, int nWords, int iBit )
{
    if ( Abc_NtkIsMappedLogic(pObj->pNtk) && Type >= 0 )
    {
        extern int Mio_LibGateSimulateOne( Mio_Gate_t * pGate, int iBits[6] );
        Mio_Library_t * pLib = (Mio_Library_t *)pObj->pNtk->pManFunc;
        int i, iBits[6];
        for ( i = 0; i < Abc_ObjFaninNum(pObj); i++ )
        {
            word * pSim0 = Vec_WrdEntryP( vSims, nWords * Abc_ObjFaninId(pObj, i) );
            iBits[i] = Abc_InfoHasBit( (unsigned*)pSim0, iBit );
        }
        return Mio_LibGateSimulateOne( Mio_LibraryReadGateById(pLib, Type), iBits );
    }
    else
    {
        word * pSim0 = Abc_ObjFaninNum(pObj) > 0 ? Vec_WrdEntryP( vSims, nWords * Abc_ObjFaninId0(pObj) ) : NULL;
        word * pSim1 = Abc_ObjFaninNum(pObj) > 1 ? Vec_WrdEntryP( vSims, nWords * Abc_ObjFaninId1(pObj) ) : NULL;
        int iBit0 = Abc_ObjFaninNum(pObj) > 0 ? Abc_InfoHasBit( (unsigned*)pSim0, iBit ) : -1;
        int iBit1 = Abc_ObjFaninNum(pObj) > 1 ? Abc_InfoHasBit( (unsigned*)pSim1, iBit ) : -1;
        assert( Type != ABC_FIN_NEG );
        if ( Type == ABC_FIN_SA0 )            return 0;
        if ( Type == ABC_FIN_SA1 )            return 1;
        if ( Type == ABC_FIN_RDOB_BUFF )      return iBit0;
        if ( Type == ABC_FIN_RDOB_NOT )       return !iBit0;
        if ( Type == ABC_FIN_RDOB_AND )       return iBit0 & iBit1;
        if ( Type == ABC_FIN_RDOB_OR )        return iBit0 | iBit1;
        if ( Type == ABC_FIN_RDOB_XOR )       return iBit0 ^ iBit1;
        if ( Type == ABC_FIN_RDOB_NAND )      return !(iBit0 & iBit1);
        if ( Type == ABC_FIN_RDOB_NOR )       return !(iBit0 | iBit1);
        if ( Type == ABC_FIN_RDOB_NXOR )      return !(iBit0 ^ iBit1);
        assert( 0 );
        return -1;
    }
}
static inline void Abc_NtkFinSimOneWord( Abc_Obj_t * pObj, int Type, Vec_Wrd_t * vSims, int nWords )
{
    if ( Abc_NtkIsMappedLogic(pObj->pNtk) )
    {
        extern void Mio_LibGateSimulate( Mio_Gate_t * pGate, word * ppFaninSims[6], int nWords, word * pObjSim );
        word * ppSims[6]; int i;
        word * pSim = Vec_WrdEntryP( vSims, nWords * Abc_ObjId(pObj) );
        assert( Type == -1 );
        for ( i = 0; i < Abc_ObjFaninNum(pObj); i++ )
            ppSims[i] = Vec_WrdEntryP( vSims, nWords * Abc_ObjFaninId(pObj, i) );
        Mio_LibGateSimulate( (Mio_Gate_t *)pObj->pData, ppSims, nWords, pSim );
    }
    else
    {
        word * pSim  = Vec_WrdEntryP( vSims, nWords * Abc_ObjId(pObj) );  int w;
        word * pSim0 = Abc_ObjFaninNum(pObj) > 0 ? Vec_WrdEntryP( vSims, nWords * Abc_ObjFaninId0(pObj) ) : NULL;
        word * pSim1 = Abc_ObjFaninNum(pObj) > 1 ? Vec_WrdEntryP( vSims, nWords * Abc_ObjFaninId1(pObj) ) : NULL;
        assert( Type != ABC_FIN_NEG );
        if ( Type == ABC_FIN_SA0 )            for ( w = 0; w < nWords; w++ ) pSim[w] = 0;
        else if ( Type == ABC_FIN_SA1 )       for ( w = 0; w < nWords; w++ ) pSim[w] = ~((word)0);
        else if ( Type == ABC_FIN_RDOB_BUFF ) for ( w = 0; w < nWords; w++ ) pSim[w] = pSim0[w];
        else if ( Type == ABC_FIN_RDOB_NOT )  for ( w = 0; w < nWords; w++ ) pSim[w] = ~pSim0[w];
        else if ( Type == ABC_FIN_RDOB_AND )  for ( w = 0; w < nWords; w++ ) pSim[w] = pSim0[w] & pSim1[w];
        else if ( Type == ABC_FIN_RDOB_OR )   for ( w = 0; w < nWords; w++ ) pSim[w] = pSim0[w] | pSim1[w];
        else if ( Type == ABC_FIN_RDOB_XOR )  for ( w = 0; w < nWords; w++ ) pSim[w] = pSim0[w] ^ pSim1[w];
        else if ( Type == ABC_FIN_RDOB_NAND ) for ( w = 0; w < nWords; w++ ) pSim[w] = ~(pSim0[w] & pSim1[w]);
        else if ( Type == ABC_FIN_RDOB_NOR )  for ( w = 0; w < nWords; w++ ) pSim[w] = ~(pSim0[w] | pSim1[w]);
        else if ( Type == ABC_FIN_RDOB_NXOR ) for ( w = 0; w < nWords; w++ ) pSim[w] = ~(pSim0[w] ^ pSim1[w]);
        else assert( 0 );
    }
}

// returns 1 if the functionality with indexes i1 and i2 is the same
static inline int Abc_NtkFinCompareSimTwo( Abc_Ntk_t * pNtk,  Vec_Int_t * vCos, Vec_Wrd_t * vSims, int nWords, int i1, int i2 )
{
	Abc_Obj_t * pObj; int i;
    assert( i1 != i2 );
   Abc_NtkForEachObjVec( vCos, pNtk, pObj, i )
    {
        word * pSim0 = Vec_WrdEntryP( vSims, nWords * Abc_ObjFaninId0(pObj) );
        if ( Abc_InfoHasBit((unsigned*)pSim0, i1) != Abc_InfoHasBit((unsigned*)pSim0, i2) )
            return 0;
    }
    
	
	return 1;
}
/*static inline int Abc_NtkFinCompareSimTwoSeq( Abc_Ntk_t ** pNtkFaults,int nFaultNum,  int iFin0, int iFin )
{
	int  equal = 1;
	int *out0;
	int *out1;
	//int *classes; 
	int nOnputs = Abc_NtkPoNum(pNtkFaults[0]);
	
	out0 = Abc_NtkSimulateSeq(pNtkFaults[iFin0 -1]);

	out1 = Abc_NtkSimulateSeq(pNtkFaults[iFin -1]);
	for (int i = 0; i < nOnputs * 50 ; i++)
	{
		if (out1[i] != out0[i])
			equal = 0;
	}
	free(out0);
	free(out1);
	
	return equal;
}*/


Gia_Man_t * Abc_NtkFinMiterToGia( Abc_Ntk_t * pNtk, Vec_Int_t * vTypes, Vec_Int_t * vCos, Vec_Int_t * vCis, Vec_Int_t * vNodes, 
                                  int iObjs[2], int Types[2], Vec_Int_t * vLits)
{
    extern Gia_Man_t * Abc_NtkAigToGia( Abc_Ntk_t * p, int fGiaSimple );
	extern int Abc_NtkToAig( Abc_Ntk_t * pNtk );
	Gia_Man_t * pNew = NULL, * pTemp;
    Abc_Obj_t * pObj; 
    Vec_Int_t * vTemp = Vec_IntAlloc( 100 );
	Vec_Int_t * vFlops = Vec_IntAlloc( 100 );
    int n, i, Type, iMiter, iLit, * pLits;
    // create AIG manager
    pNew = Gia_ManStart( 1000 );
    pNew->pName = Abc_UtilStrsav( pNtk->pName );
    pNew->pSpec = Abc_UtilStrsav( pNtk->pSpec );
    Gia_ManHashStart( pNew );
	
    // create inputs
    Abc_NtkForEachObjVec( vCis, pNtk, pObj, i )
    {
		//Vec_IntPrint(vCis);
		iLit = Gia_ManAppendCi(pNew);
		//printf("objec ID %d  iLit %d   \n",Abc_ObjId(pObj) , iLit);
        for ( n = 0; n < 2; n++ )
        {
			//Vec_IntPrint(vLits);
			if ( iObjs[n] != (int)Abc_ObjId(pObj) ){
                Vec_IntWriteEntry( vLits, Abc_Var2Lit(Abc_ObjId(pObj), n), iLit );
				
				//printf("Check print Abc_Var2Lit(Abc_ObjId(pObj), n) = %d  , n = %d  iLit = %d, iObjs[n]  = %d \n ",Abc_Var2Lit(Abc_ObjId(pObj), n), n, iLit, iObjs[n]  );
				//Vec_IntPrint(vLits);
			}
            else if ( Types[n] != ABC_FIN_NEG ){
                Vec_IntWriteEntry( vLits, Abc_Var2Lit(Abc_ObjId(pObj), n), Abc_NtkFinSimOneLit(pNew, pObj, Types[n], vLits, n, vTemp) );
				
				//printf("objec ID %d   FindSim %d   \n",Abc_ObjId(pObj) ,  Abc_NtkFinSimOneLit(pNew, pObj, Types[n], vLits, n, vTemp));
				//Vec_IntPrint(vLits);
			}
			else{ // if ( iObjs[n] == (int)Abc_ObjId(pObj) && Types[n] == ABC_FIN_NEG )
                Vec_IntWriteEntry( vLits, Abc_Var2Lit(Abc_ObjId(pObj), n), Abc_LitNot(iLit) );
				
			}
		}
    }
	
    // create internal nodes
    Abc_NtkForEachObjVec( vNodes, pNtk, pObj, i )
    {
		//Vec_IntPrint(vNodes);
		Type = Abc_NtkIsMappedLogic(pNtk) ? Mio_GateReadCell((Mio_Gate_t *)pObj->pData) : Vec_IntEntry(vTypes, Abc_ObjId(pObj));
        for ( n = 0; n < 2; n++ )
        {
            if ( iObjs[n] != (int)Abc_ObjId(pObj) ){
                Vec_IntWriteEntry( vLits, Abc_Var2Lit(Abc_ObjId(pObj), n), Abc_NtkFinSimOneLit(pNew, pObj, Type, vLits, n, vTemp) );
				//printf("objec ID %d   FindSim %d   \n",Abc_ObjId(pObj) ,  Abc_NtkFinSimOneLit(pNew, pObj, Type, vLits, n, vTemp));
				//Vec_IntPrint(vLits);
			}
            else if ( Types[n] != ABC_FIN_NEG )
                Vec_IntWriteEntry( vLits, Abc_Var2Lit(Abc_ObjId(pObj), n), Abc_NtkFinSimOneLit(pNew, pObj, Types[n], vLits, n, vTemp) );
            else // if ( iObjs[n] == (int)Abc_ObjId(pObj) && Types[n] == ABC_FIN_NEG )
                Vec_IntWriteEntry( vLits, Abc_Var2Lit(Abc_ObjId(pObj), n), Abc_LitNot(Abc_NtkFinSimOneLit(pNew, pObj, Type, vLits, n, vTemp)) );
        }
    }
	
    // create comparator
    iMiter = 0;
    Abc_NtkForEachObjVec( vCos, pNtk, pObj, i )
    {
   
		pLits  = Vec_IntEntryP( vLits, Abc_Var2Lit(Abc_ObjFaninId0(pObj), 0) );
        iLit   = Gia_ManHashXor( pNew, pLits[0], pLits[1] );
        iMiter = Gia_ManHashOr( pNew, iMiter, iLit );
    }
    //Gia_ManPrint(pNew);
	Gia_ManAppendCo( pNew, iMiter );
	
	
    // perform cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    Vec_IntFree( vTemp );
    Vec_IntFree( vFlops );
	
    return pNew;
}

void Abc_NtkFinSimulateOne( Abc_Ntk_t * pNtk, Vec_Int_t * vTypes, Vec_Int_t * vCos, Vec_Int_t * vCis, Vec_Int_t * vNodes, Vec_Wec_t * vMap2, Vec_Int_t * vPat, Vec_Wrd_t * vSims, int nWords, Vec_Int_t * vPairs, Vec_Wec_t * vRes, int iLevel, int iItem )
{
	
	Abc_Obj_t * pObj; 
    Vec_Int_t * vClass, * vArray;
    int i, Counter = 0;
    int nItems = Vec_WecSizeSize(vRes);
    assert( nItems == Vec_WecSizeSize(vMap2) );
    assert( nItems <= 128 * nWords );
    // assign inputs
    assert( Vec_IntSize(vPat) == Vec_IntSize(vCis) );
	
    Abc_NtkForEachObjVec( vCis, pNtk, pObj, i )
    {
        int w, iObj = Abc_ObjId( pObj );
        word Init = Vec_IntEntry(vPat, i) ? ~((word)0) : 0;
        word * pSim = Vec_WrdEntryP( vSims, nWords * Abc_ObjId(pObj) );
        for ( w = 0; w < nWords; w++ )
            pSim[w] = Init;
        vArray = Vec_WecEntry(vMap2, iObj);
        if ( Vec_IntSize(vArray) > 0 )
        {
            int k, iFin, Index, iObj, Type;
            Vec_IntForEachEntryDouble( vArray, iFin, Index, k )
            {
               // assert( Index < 64 );
                iObj = Vec_IntEntry( vPairs, 2*iFin );
                assert( iObj == (int)Abc_ObjId(pObj) );
                Type = Vec_IntEntry( vPairs, 2*iFin+1 );
                assert( Type == ABC_FIN_NEG || Type == ABC_FIN_SA0 || Type == ABC_FIN_SA1 );
                if ( Type == ABC_FIN_NEG || Abc_InfoHasBit((unsigned *)pSim, Index) != Abc_NtkFinSimOneBit(pObj, Type, vSims, nWords, Index) )
                    Abc_InfoXorBit( (unsigned *)pSim, Index );
                Counter++;
            }
        }
    }
	
    // simulate internal nodes
    Abc_NtkForEachObjVec( vNodes, pNtk, pObj, i )
    {
		int iObj = Abc_ObjId( pObj );
        int Type = Abc_NtkIsMappedLogic(pNtk) ? -1 : Vec_IntEntry( vTypes, iObj );
        word * pSim = Vec_WrdEntryP( vSims, nWords * Abc_ObjId(pObj) );
        Abc_NtkFinSimOneWord( pObj, Type, vSims, nWords );
        vArray = Vec_WecEntry(vMap2, iObj);
        if ( Vec_IntSize(vArray) > 0 )
        {
            int k, iFin, Index, iObj, Type;
            Vec_IntForEachEntryDouble( vArray, iFin, Index, k )
            {
                assert( Index < 64 * nWords );
                iObj = Vec_IntEntry( vPairs, 2*iFin );
                assert( iObj == (int)Abc_ObjId(pObj) );
                Type = Vec_IntEntry( vPairs, 2*iFin+1 );
                if ( Type == ABC_FIN_NEG || Abc_InfoHasBit((unsigned *)pSim, Index) != Abc_NtkFinSimOneBit(pObj, Type, vSims, nWords, Index) )
                    Abc_InfoXorBit( (unsigned *)pSim, Index );
                Counter++;
            }
        }
    }
    //assert( nItems == 2*Counter );
	//transfer the latch values
	
    // confirm no refinement
    Vec_WecForEachLevelStop( vRes, vClass, i, iLevel+1 )
    {
        int k, iFin, Index, Value;
        int Index0 = Vec_IntEntry( vClass, 1 );
	
        Vec_IntForEachEntryDoubleStart( vClass, iFin, Index, k, 2 )
        {
            if ( i == iLevel && k/2 >= iItem )
                break;
            //printf( "Double-checking pair %d and %d\n", iFin0, iFin );
				Value = Abc_NtkFinCompareSimTwo( pNtk, vCos, vSims, nWords, Index0, Index );
				assert( Value ); // the same value
        }
    }

    // check refinement
    Vec_WecForEachLevelStart( vRes, vClass, i, iLevel )
    {
        int k, iFin, Index, Value, Index0 = Vec_IntEntry(vClass, 1);
        int j = (i == iLevel) ? 2*iItem : 2;
        Vec_Int_t * vNewClass = NULL;
		Vec_IntForEachEntryDoubleStart( vClass, iFin, Index, k, j )
        { 
			Value = Abc_NtkFinCompareSimTwo( pNtk, vCos, vSims, nWords, Index0, Index );

			if ( Value )  // the same value
            {
				Vec_IntWriteEntry( vClass, j++, iFin );
                Vec_IntWriteEntry( vClass, j++, Index );
				
                continue;
            }
            // create new class
            vNewClass = vNewClass ? vNewClass : Vec_WecPushLevel( vRes );
            Vec_IntPushTwo( vNewClass, iFin, Index );  // index and first entry
            vClass = Vec_WecEntry( vRes, i );
        }
        Vec_IntShrink( vClass, j );
    }
	
}

/**Function*************************************************************

  Synopsis    [Check equivalence using SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkFinCheckPair( Abc_Ntk_t * pNtk, Vec_Int_t * vTypes, Vec_Int_t * vCos, Vec_Int_t * vCis, Vec_Int_t * vNodes, int iObjs[2], int Types[2], Vec_Int_t * vLits )
{

   Gia_Man_t * pGia = Abc_NtkFinMiterToGia( pNtk, vTypes, vCos, vCis, vNodes, iObjs, Types, vLits );
   //Gia_ManPrint(pGia);
  // printf("****************finished construct miter \n");
    if ( Gia_ManAndNum(pGia) == 0 && Gia_ObjIsConst0(Gia_ObjFanin0(Gia_ManCo(pGia, 0))) )
    {
        Vec_Int_t * vPat = Gia_ObjFaninC0(Gia_ManCo(pGia, 0)) ? Vec_IntStart(Vec_IntSize(vCis)) : NULL;
        Gia_ManStop( pGia );
        return vPat;
    }
    else
    {
        Cnf_Dat_t * pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( pGia, 8, 0, 1, 0, 0 );
        sat_solver * pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
        if ( pSat == NULL )
        {
            Gia_ManStop( pGia );
            Cnf_DataFree( pCnf );
            return NULL;
        }
        else
        {
            int i, nConfLimit = 10000;
            Vec_Int_t * vPat = NULL;
            int status, iVarBeg = pCnf->nVars - Gia_ManPiNum(pGia);// - 1;
            //Gia_AigerWrite( pGia, "temp_detect.aig", 0, 0 );
            Gia_ManStop( pGia );
            Cnf_DataFree( pCnf );
            status = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)nConfLimit, 0, 0, 0 );
            if ( status == l_Undef )
                vPat = Vec_IntAlloc(0);
            else if ( status == l_True )
            {
                vPat = Vec_IntAlloc( Vec_IntSize(vCis) );
                for ( i = 0; i < Vec_IntSize(vCis); i++ )
                    Vec_IntPush( vPat, sat_solver_var_value(pSat, iVarBeg+i) );
            }
            //printf( "%d ", sat_solver_nconflicts(pSat) );
            sat_solver_delete( pSat );
			
            return vPat;
        }
    }
}



/**Function*************************************************************

  Synopsis    [Refinement of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFinLocalSetup( Vec_Int_t * vPairs, Vec_Int_t * vList, Vec_Wec_t * vMap2, Vec_Int_t * vResArray )
{
    int i, iFin;
    Vec_IntClear( vResArray );
    Vec_IntForEachEntry( vList, iFin, i )
    {
        int iObj = Vec_IntEntry( vPairs, 2*iFin );
        Vec_Int_t * vArray = Vec_WecEntry( vMap2, iObj );
        Vec_IntPushTwo( vArray, iFin, i );
        Vec_IntPushTwo( vResArray, iFin, i );
    }
}
void Abc_NtkFinLocalSetdown( Vec_Int_t * vPairs, Vec_Int_t * vList, Vec_Wec_t * vMap2 )
{
    int i, iFin;
    Vec_IntForEachEntry( vList, iFin, i )
    {
        int iObj = Vec_IntEntry( vPairs, 2*iFin );
        Vec_Int_t * vArray = Vec_WecEntry( vMap2, iObj );
        Vec_IntClear( vArray );
    }
}
int Abc_NtkFinRefinement( Abc_Ntk_t * pNtk,Abc_Ntk_t ** pNtkFaults,int nFaultNum,Vec_Wec_t * vClassesSeq, Vec_Int_t * vTypes, Vec_Int_t * vCos, Vec_Int_t * vCis, Vec_Int_t * vNodes, 
                          Vec_Int_t * vPairs, Vec_Int_t * vList, Vec_Wec_t * vMap2, Vec_Wec_t * vResult,  int fSeq)
{
    Vec_Wec_t * vRes  = Vec_WecAlloc( 100 );
    int nWords = Abc_Bit6WordNum( Vec_IntSize(vList) );
    Vec_Wrd_t * vSims = Vec_WrdStart( nWords * Abc_NtkObjNumMax(pNtk) );  // simulation info for each object
    Vec_Int_t * vLits = Vec_IntStart( 2*Abc_NtkObjNumMax(pNtk) );         // two literals for each object
    Vec_Int_t * vPat, * vClass, * vArray;  
    int i, k, iFin, Index, nCalls = 0;
    // prepare
    vArray = Vec_WecPushLevel( vRes );
    Abc_NtkFinLocalSetup( vPairs, vList, vMap2, vArray );

    // explore the classes
	if ( fSeq )
	{
		vRes = vClassesSeq;
		
		//printf("Sequential Class refinement \n");
		int nNumClsOr = Vec_WecSize(vRes);
		int nNew = nNumClsOr;
		int cnt = 0;
		Vec_WecForEachLevelStartStop(vRes, vClass, i,0, nNumClsOr)
		{
			
			nNew = nNew + cnt; cnt = 0;
			int iFin0  = Vec_IntEntry( vClass, 0 );
			 Vec_IntForEachEntryDoubleStart( vClass, iFin, Index, k, 2 )
			 {
				 int nValue;
				nValue = Abc_NtkEquivDsec(pNtkFaults[iFin0-1], pNtkFaults[iFin-1]);
				if (nValue)
					continue;// keep the fault where it is in class
				assert( Vec_IntEntry(vClass, k) == iFin );
				if (nValue == 0)
				{
					Vec_IntDrop( vClass, k+1 );
					Vec_IntDrop( vClass, k );
					k -= 2;	
					int fFound = 0;
					Vec_Int_t * vClass2;
					int l;
				
					Vec_WecForEachLevelStart(vRes, vClass2, l, nNew)
					{
						int iFin1 = Vec_IntEntry(vClass2, 0);
						nValue = Abc_NtkEquivDsec(pNtkFaults[iFin-1], pNtkFaults[iFin1-1]);
						if (nValue)
						{
							Vec_IntPushTwo( vClass2, iFin, 0 );
							fFound = 1;
							break;
						}
					}
					if (fFound == 0)
					{
						Vec_Int_t * vNewClass = Vec_WecPushLevel(vRes);
						Vec_IntPushTwo( vNewClass, iFin, 0 );
						cnt ++;
					}
				}
				
			 }
		}
		
	}

	else
	{
	//printf("Combination Class refinement \n");
    Vec_WecForEachLevel( vRes, vClass, i )
    {
		int iFin0  = Vec_IntEntry( vClass, 0 );
		//Vec_WecPrint(vRes,0);
        Vec_IntForEachEntryDoubleStart( vClass, iFin, Index, k, 2 )
        {
			int Objs[2]  = { Vec_IntEntry(vPairs, 2*iFin0),   Vec_IntEntry(vPairs, 2*iFin)   }; 
            int Types[2] = { Vec_IntEntry(vPairs, 2*iFin0+1), Vec_IntEntry(vPairs, 2*iFin+1) }; 
            nCalls++;
            //printf( "Checking pair %d and %d.\n", iFin0, iFin );	
            vPat = Abc_NtkFinCheckPair( pNtk, vTypes, vCos, vCis, vNodes, Objs, Types, vLits );
            
			if ( vPat == NULL ) // proved
                continue;
            assert( Vec_IntEntry(vClass, k) == iFin );
		
			if  (Vec_IntSize(vPat) == 0)  
            {
				Vec_Int_t * vNewClass = Vec_WecPushLevel( vRes );
                Vec_IntPushTwo( vNewClass, iFin, Index );  // index and first entry
                vClass = Vec_WecEntry( vRes, i );
                Vec_IntDrop( vClass, k+1 );
                Vec_IntDrop( vClass, k );
            }
			
            else // resimulate and refine
                Abc_NtkFinSimulateOne( pNtk,vTypes, vCos, vCis, vNodes, vMap2, vPat, vSims, nWords, vPairs, vRes, i, k/2 );
            Vec_IntFree( vPat );
            // make sure refinement happened (k'th entry is now absent or different)
            vClass = Vec_WecEntry( vRes, i );
          //  assert( Vec_IntSize(vClass) <= k || Vec_IntEntry(vClass, k) != iFin );
            k -= 2;
           
        }
    }
	}
    // unprepare
    Abc_NtkFinLocalSetdown( vPairs, vList, vMap2 );
    // reload proved equivs into the final array
    Vec_WecForEachLevel( vRes, vArray, i )
    {
        assert( Vec_IntSize(vArray) % 2 == 0 );
        if ( Vec_IntSize(vArray) <= 2 )
            continue;
        vClass = Vec_WecPushLevel( vResult );
        Vec_IntForEachEntryDouble( vArray, iFin, Index, k )
            Vec_IntPush( vClass, iFin );
    }
    Vec_WecFree( vRes );
    Vec_WrdFree( vSims );
    Vec_IntFree( vLits );
    return nCalls;
}

/**Function*************************************************************

  Synopsis    [Detecting classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_ObjFinGateType( Abc_Obj_t * pNode )
{
    char * pSop = (char *)pNode->pData;
    if ( !strcmp(pSop, "1 1\n") )         return ABC_FIN_RDOB_BUFF;
    if ( !strcmp(pSop, "0 1\n") )         return ABC_FIN_RDOB_NOT;
    if ( !strcmp(pSop, "11 1\n") )        return ABC_FIN_RDOB_AND;
    if ( !strcmp(pSop, "11 0\n") )        return ABC_FIN_RDOB_NAND;
    if ( !strcmp(pSop, "00 0\n") )        return ABC_FIN_RDOB_OR;
    if ( !strcmp(pSop, "00 1\n") )        return ABC_FIN_RDOB_NOR;
    if ( !strcmp(pSop, "01 1\n10 1\n") )  return ABC_FIN_RDOB_XOR;
    if ( !strcmp(pSop, "11 1\n00 1\n") )  return ABC_FIN_RDOB_NXOR;
    return ABC_FIN_NONE;
}
int Abc_NtkFinCheckTypesOk( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Abc_NtkForEachNode( pNtk, pObj, i )
        if ( Abc_ObjFinGateType(pObj) == ABC_FIN_NONE )
            return i;
    return 0;
}
int Abc_NtkFinCheckTypesOk2( Abc_Ntk_t * pNtk )
{
    Mio_Library_t * pLib = (Mio_Library_t *)pNtk->pManFunc;
    int i, iObj, Type;
    Vec_IntForEachEntryDoubleStart( pNtk->vFins, iObj, Type, i, 2 )
    {
        Abc_Obj_t * pObj = Abc_NtkObj( pNtk, iObj );
        Mio_Gate_t * pGateFlt, * pGateObj = (Mio_Gate_t *)pObj->pData;
        if ( Type < 0 ) // SA0, SA1, NEG
            continue;
        pGateFlt = Mio_LibraryReadGateById( pLib, Type );
        if ( Mio_GateReadPinNum(pGateFlt) < 1 )
            continue;
        if ( Mio_GateReadPinNum(pGateObj) != Mio_GateReadPinNum(pGateFlt) )
            return iObj;
    }
    return 0;
}
Vec_Int_t * Abc_NtkFinComputeTypes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Int_t * vObjs = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
        Vec_IntWriteEntry( vObjs, Abc_ObjId(pObj), Abc_ObjFinGateType(pObj) );
    return vObjs;
}
Vec_Int_t * Abc_NtkFinComputeObjects( Vec_Int_t * vPairs, Vec_Wec_t ** pvMap, int nObjs )
{
    int i, iObj, Type;
    Vec_Int_t * vObjs = Vec_IntAlloc( 100 );
    *pvMap = Vec_WecStart( nObjs );
    Vec_IntForEachEntryDoubleStart( vPairs, iObj, Type, i, 2 )
    {
        Vec_IntPush( vObjs, iObj );
		//printf("%d  %d \n", iObj, i/2);
        Vec_WecPush( *pvMap, iObj, i/2 );
    }
    Vec_IntUniqify( vObjs );
    return vObjs;
}
Vec_Int_t * Abc_NtkFinCreateList( Vec_Wec_t * vMap, Vec_Int_t * vClass )
{
    int i, iObj;
	//Vec_WecPrint(vMap,0);
    Vec_Int_t * vList = Vec_IntAlloc( 100 );
    Vec_IntForEachEntry( vClass, iObj, i )
        Vec_IntAppend( vList, Vec_WecEntry(vMap, iObj) );
    return vList;
}
int Abc_NtkFinCountPairs( Vec_Wec_t * vClasses )
{
    int i, Counter = 0;
    Vec_Int_t * vLevel;
    Vec_WecForEachLevel( vClasses, vLevel, i )
        Counter += Vec_IntSize(vLevel) - 1;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [PregroupIteration]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/



Vec_Wec_t * Abc_NtkSimulateValue(Abc_Ntk_t **fcircNtk, int nFaultNum, int nFrames, int* M, int seed, Vec_Int_t * vGroupRow, int grp_len)
{
	//to generata 
	int j, i, outputs;
	int * out;
	Vec_Wec_t * wSimOut;
	int ind = 0;
	//printf("gen_matrix grp_len = %d \n\n", grp_len);
	outputs = Abc_NtkPoNum(*fcircNtk);
	// M is number of simulation result of one circuit output over nFrames
	*M = outputs*nFrames;
	// final_matrix contains simulation of all fault circuits
	wSimOut = Vec_WecAlloc(outputs * nFrames * nFaultNum);
	
	for (j = 0; j < grp_len; j++)
	{
		//printf("%d \t", group[j]);
		// do simulation for circuit over nFrames. Result is list of outputs
		out = Abc_NtkSimulateSeq(fcircNtk[Vec_IntEntry(vGroupRow,j)], nFrames, outputs, seed);
		Vec_Int_t * vSimulation;
		vSimulation = Vec_WecPushLevel(wSimOut);
		for (i = 0; i < outputs*nFrames; i++)
		{
			// Copy simulation result to final_matrix
			Vec_IntPush(vSimulation, out[i]);
			//printf("out[%d] %d \n",i, out[i]);
			ind++;
			
		}
		free(out);
	}
	//printf("\n");
	return wSimOut;
}

int Abc_NtkPregroupIteration(Abc_Ntk_t **fcircNtk, int fl_num, int nFrames, Vec_Wec_t * wGroups,  int row,  int seed)
{
	int i, j, m;

	Vec_Wec_t * wSimulation;

	// Get length of group at row

	int rows = Vec_WecSize(wGroups);
	Vec_Int_t * vClasses = Vec_WecEntry(wGroups, row);
	int grp_len = Vec_IntSize(vClasses);
	//printf("rows = %d grp_len =%d \n", rows, grp_len);
	
	//static int c_cnt = 0;
	//printf("Call: %d\n",c_cnt); c_cnt++;
	
	//Create wSimulation is vector(size grp_len) of vector int(size m)
	wSimulation = Abc_NtkSimulateValue(fcircNtk, fl_num, nFrames, &m, seed, vClasses, grp_len);
	//Vec_WecPrint(wSimulation,0);
	
	Vec_Int_t * vRow = Vec_IntAllocArrayCopy(vClasses->pArray, Vec_WecEntry(wGroups, row)->nSize);// fault id is not arrange
	
	Vec_IntShrink(vClasses, 1);
	
	//vMap is a map, that map from fault id to index of circuit in vClasses
	Vec_Int_t * vMap = Vec_IntAlloc(fl_num);
	int Entry;
	Vec_IntForEachEntry(vRow, Entry, i)
		Vec_IntSetEntry(vMap, Entry, i);
		
	
	for (i = 1; i < Vec_IntSize(vRow); i++){
		int find = 0;
		if (1 == Vec_IntEqual(Vec_WecEntry(wSimulation, i), Vec_WecEntry(wSimulation, 0))){
			Vec_WecPush(wGroups, row, Vec_IntEntry(vRow, i));		
			find = 1;
		}
		else{
			Vec_Int_t * vClass;
			Vec_WecForEachLevelStart(wGroups, vClass, j, rows){
				int nInd0 = Vec_IntEntry(vClass,0);
				
				if (1 == Vec_IntEqual(Vec_WecEntry(wSimulation, i), Vec_WecEntry(wSimulation, Vec_IntEntry(vMap, nInd0)))) {
					Vec_IntPush(vClass, Vec_IntEntry(vRow, i));
				find = 1;
				break;
				}
			}
		}
		if (1 != find)
		{
		
			Vec_Int_t * vClassNew = Vec_WecPushLevel(wGroups);

			Vec_IntPush(vClassNew, Vec_IntEntry(vRow, i));			

		}
	}
	

	
	Vec_WecFree(wSimulation);
	Vec_IntFree(vMap);
	Vec_IntFree(vRow);
	// if don't have any new group, then return 1
	if (rows == Vec_WecSize(wGroups))
		return 1;
	else
		return 0;
}
void Abc_Ntk_GroupIndex(Vec_Wec_t * wGroups, Vec_Int_t* vPregroup_faults)
{

	int i,j, Entry;
	Vec_Int_t * vClass;
	Vec_WecForEachLevel( wGroups, vClass, i ){
		int index = Vec_IntEntry(vClass,0);
		if(Vec_IntSize(vClass) == 1)
			continue;
		Vec_IntForEachEntry(vClass, Entry, j)
			Vec_IntSetEntry(vPregroup_faults, Entry, index);
	}
		
	
}

Vec_Int_t * Abc_NtlFaultPregroup(Abc_Ntk_t **fcircNtk, int nFaultNum){
	
	int i, j;
	int  max_group;
	int first_tst_num = 50;
	int iter_num = 50;
	int min_el = 5;
	int max_el = 20;
	int threshold = 3;
	int nFrames = 50;
	
	// initialization
	
	Vec_Int_t * vPregroup_faults = Vec_IntAlloc(nFaultNum);
	vPregroup_faults = Vec_IntStartFull( nFaultNum );

	Vec_Int_t * vFaultsID = Vec_IntAlloc(nFaultNum);
	for (j = 0; j < nFaultNum; j++)
	{
		Vec_IntPush(vFaultsID,j);
	}

	Vec_Wec_t * wGroups = Vec_WecAlloc(nFaultNum);
	
	for (j = 0; j < nFaultNum; j++)
	{
			Vec_WecPush(wGroups, 0, Vec_IntEntry(vFaultsID, j));
	}

	
	
	// First row of maxtrix is fault ids of all valid fault circuits
	// ex: nFaultNum = 8, only has 6 fault circuits
	// Groups = [[0 1 2 4 6 7 _ _],
	// 	 		 [_ _ _ _ _ _ _ _],
	// 	 		 [_ _ _ _ _ _ _ _],
	// 	 		 [_ _ _ _ _ _ _ _],
	// 	 		 [_ _ _ _ _ _ _ _],
	// 	 		 [_ _ _ _ _ _ _ _],
	// 	 		 [_ _ _ _ _ _ _ _],
	// 	 		 [_ _ _ _ _ _ _ _]]

	
	// Iteration
	printf("    Do Iteration 0 \n");
	
	Abc_NtkPregroupIteration(fcircNtk, nFaultNum, first_tst_num,  wGroups, 0, 0);
	
	max_group = 0;
	Vec_Int_t * vgropmax;
	Vec_WecForEachLevel(wGroups, vgropmax, i)
	{
		if (max_group < Vec_WecLevelSize(wGroups, i))
			max_group = Vec_WecLevelSize(wGroups, i);
	}
	
	Vec_Int_t * vIteration =  Vec_IntStart(nFaultNum);
	// Number of iteration do the pregroup 
	for (i = 0; i < iter_num; i++)
	{
		// if current maximum number elements of groups small enough, stop iterating
		if (max_group < max_el)
			break;
		for (j = 0; j < Vec_WecSize(wGroups); j++)
		{
			// if pregroup at j < min_el, ignor this group
			if (Vec_WecLevelSize(wGroups, j) < min_el)
				continue;
			// if this row had been processed more than threshold times, 
			// without new group found, then ignore this row
			if (Vec_IntEntry(vIteration, j) >= threshold)
				continue;
			// Do pregroup_iteration for row j, with new seed number ((i + 1)*(j + 1) + 10))
			// If no new group had been found for row j, 
			// then increase number of processed vIteration.
			// Else, reset to_process counter
			if (Abc_NtkPregroupIteration(fcircNtk, nFaultNum, nFrames, wGroups,  j,  (i + 1)*(j + 1) + 10)){
				//Vec_IntEntry(vIteration, j) + 1;
				Vec_IntSetEntry(vIteration, j, Vec_IntEntry(vIteration, j) + 1);
			}
			else 
				Vec_IntSetEntry(vIteration, j, 0);
		}

		max_group = 0;
		for (j = 0; j < Vec_WecSize(wGroups); j++)
		{
			if (Vec_WecLevelSize(wGroups, j) < 2)
				continue;
			if (Vec_IntEntry(vIteration, j)  >= threshold)
				continue;

			if (max_group < Vec_WecLevelSize(wGroups, j))
			{
				max_group = Vec_WecLevelSize(wGroups, j);
			}
		}	

	}

	Abc_Ntk_GroupIndex( wGroups, vPregroup_faults );
	
	Vec_IntFree(vFaultsID);
	Vec_WecFree(wGroups);
	return vPregroup_faults;
}



Vec_Wec_t * Abc_NtkDetectFinClassesSeq(Abc_Ntk_t **fcircNtk, int nFaultNum) {
	
	Vec_Int_t * vFaultGroup = Vec_IntAlloc(nFaultNum);
	vFaultGroup = Abc_NtlFaultPregroup(fcircNtk, nFaultNum );
	int i, j;
	Vec_Wec_t * vRes = Vec_WecAlloc(1000) ;
	Vec_Int_t * vClass = Vec_IntAlloc(10000);
	vClass = Vec_WecPushLevel( vRes );
	for (j = 1; j < nFaultNum+1; j++)
	{
		int nEqual = 0 ; 
		 if (Vec_IntEntry(vFaultGroup,j-1) == -1)
			 continue;
		
		Vec_WecForEachLevel( vRes, vClass, i )
		{	
			if (Vec_IntSize(vClass) > 0)
			{
				 int iFin0 = Vec_IntEntry( vClass, 0 );
				 if (Vec_IntEntry(vFaultGroup,j-1) == Vec_IntEntry(vFaultGroup,iFin0-1))
				 {
					 nEqual = 1;
					 break;
				 }
				 else
					 nEqual = 0;
			}
			else
			{
				nEqual = 1;
				break;
			}
		}			
				 
		if (nEqual)
			 Vec_IntPushTwo( vClass, j, 0 );
		
		else 
		{
			Vec_Int_t * vNewClass = Vec_WecPushLevel( vRes );
				Vec_IntPushTwo( vNewClass, j, 0 );  
		}
					
	}
	Vec_IntFree(vFaultGroup);

	return vRes;
}


Abc_Ntk_t * Abc_NtkInjectFlt (Abc_Ntk_t * pNtk, struct Abc_Ntk_FaultDescr fault, int zero_replace )
{
	int i;
	int fix_num = 0;
	int nodeType = 0;
	Abc_Ntk_t * pNtkF;
	Abc_Obj_t * pObj;
	 pNtkF = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
	pNtkF = Abc_NtkDup(pNtk);
	int intem, intem0, intem1, outtem0, outtem;
	Abc_NtkForEachPi(pNtkF, pObj, i )
	{
		intem  = atoi (Abc_ObjName(pObj));
		if (intem == fault.node) 
			nodeType = 1;
		
	}
	
	Abc_NtkForEachPo(pNtkF, pObj, i )
	{
			outtem0 = atoi (Abc_ObjName(pObj));
	
			if (outtem0 == fault.node) 
				nodeType = 2;
	}
	
	Abc_NtkForEachNode(pNtkF, pObj, i )
	{
			//skip PI/PO nodes
		if ( Abc_NodeIsConst(pObj) )
           continue;	
			
		if (Abc_ObjIsNode (pObj)){
			int nFanins;
			nFanins = Abc_ObjFaninNum(pObj);
		
		if (nFanins == 1)
		{
			outtem = atoi (Abc_ObjName(Abc_NtkObj(pNtk, i) ));
			
			intem0 = atoi (Abc_ObjName(Abc_ObjFanin0(Abc_NtkObj(pNtk, i))));
			intem1 = 0;
		}
		else
		{
			outtem = atoi (Abc_ObjName(Abc_NtkObj(pNtk, i) ));
			intem0 = atoi (Abc_ObjName(Abc_ObjFanin0(Abc_NtkObj(pNtk, i))));
			intem1 = atoi (Abc_ObjName(Abc_ObjFanin1(Abc_NtkObj(pNtk, i))));
		}
			
		if (nodeType == 0) {
			if (intem0 == fault.node || intem1 == fault.node || outtem == fault.node) {
				nodeType = 3;
			}
		
		}
	}
	}
	
	// Check possible Faults of data
	if (nodeType == 0) {
		printf("Unknown Type for node: %d", fault.node);
		exit(0);
	}

	if (nodeType == 1 && fault.Type != SA0 && fault.Type != SA1 && fault.Type != NEG) {
		printf("Unexpected fault Type %d for input node", fault.node);
		exit(0);
	}
	// Inject Fault in elements
	Abc_NtkForEachNode(pNtkF, pObj, i ) {
		
		 if (fault.Type == RDOB_AND && fault.node == atoi (Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			Abc_ObjSetData( pObj, Abc_SopCreateAnd((Mem_Flex_t *)pNtk->pManFunc, Abc_ObjFaninNum(pObj), NULL) );
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NAND && fault.node == atoi (Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			Abc_ObjSetData( pObj, Abc_SopCreateNand((Mem_Flex_t *)pNtk->pManFunc, Abc_ObjFaninNum(pObj)) );
			fix_num += 1;
		}
		else if (fault.Type == RDOB_OR && fault.node == atoi (Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			 Abc_ObjSetData( pObj, Abc_SopCreateOr((Mem_Flex_t *)pNtk->pManFunc, Abc_ObjFaninNum(pObj), NULL) );
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NOR && fault.node == atoi(Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			 Abc_ObjSetData( pObj, Abc_SopCreateNor((Mem_Flex_t *)pNtk->pManFunc, Abc_ObjFaninNum(pObj)) );
			fix_num += 1;
		}
		else if (fault.Type == RDOB_XOR && fault.node == atoi(Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			 Abc_ObjSetData( pObj, Abc_SopCreateXor((Mem_Flex_t *)pNtk->pManFunc, Abc_ObjFaninNum(pObj)) );
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NXOR && fault.node == atoi(Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			Abc_ObjSetData( pObj, Abc_SopCreateNxor((Mem_Flex_t *)pNtk->pManFunc, Abc_ObjFaninNum(pObj)) );
			fix_num += 1;
		}
		else if (fault.Type == RDOB_NOT && fault.node == atoi(Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			Abc_ObjSetData( pObj, Abc_SopCreateInv((Mem_Flex_t *)pNtk->pManFunc) );
			fix_num += 1;
		}
		else if (fault.Type == RDOB_BUFF && fault.node == atoi(Abc_ObjName(Abc_NtkObj(pNtk, i) ))) {
			  Abc_ObjSetData( pObj, Abc_SopCreateBuf((Mem_Flex_t *)pNtk->pManFunc) );
			fix_num += 1;
		}
	}
	
	return pNtkF;
}

Vec_Wec_t * Abc_NtkDetectFinClasses1( Abc_Ntk_t * pNtk, Abc_Ntk_t ** pNtkFaults, int nFaultNum,Vec_Wec_t * vClassesSeq, int fVerbose, int fSeq)
{
	
	Abc_Obj_t * pObj;
    Vec_Int_t * vTypes = NULL; // gate types
    Vec_Int_t * vPairs;        // original info as a set of pairs (ObjId, TypeId)
    Vec_Int_t * vObjs;         // all those objects that have some fin 
    Vec_Wec_t * vMap;          // for each object, the set of fins
    Vec_Wec_t * vMap2;         // for each local object, the set of pairs (Info, Index)
   // Vec_Wec_t * vClasses;      // classes of objects
  //  Vec_Wec_t * vCoSets;       // corresponding CO sets
    Vec_Int_t * vClass;        // one class
    Vec_Int_t * vCoSet;        // one set of COs
    Vec_Int_t * vCiSet;        // one set of CIs
    Vec_Int_t * vNodeSet;      // one set of nodes
    Vec_Int_t * vList;         // one info list
    Vec_Wec_t * vResult;       // resulting equivalences
    int i, iObj, nCalls;
    if ( pNtk->vFins == NULL )
    {
        printf( "Current network does not have the required info.\n" );
        return NULL;
    }
    assert( Abc_NtkIsSopLogic(pNtk) || Abc_NtkIsMappedLogic(pNtk) );
    if ( Abc_NtkIsSopLogic(pNtk) )
    {
        iObj = Abc_NtkFinCheckTypesOk(pNtk);
        if ( iObj )
        {
            printf( "Current network contains unsupported gate types (for example, see node \"%s\").\n", Abc_ObjName(Abc_NtkObj(pNtk, iObj)) );
            return NULL;
        }
        vTypes   = Abc_NtkFinComputeTypes( pNtk );
    }
    else if ( Abc_NtkIsMappedLogic(pNtk) )
    {
        iObj = Abc_NtkFinCheckTypesOk2(pNtk);
        if ( iObj )
        {
            printf( "Current network has mismatch between mapped gate size and fault gate size (for example, see node \"%s\").\n", Abc_ObjName(Abc_NtkObj(pNtk, iObj)) );
            return NULL;
        }
    }
    else assert( 0 );
	
    // collect data
    vPairs   = pNtk->vFins;
    vObjs    = Abc_NtkFinComputeObjects( vPairs, &vMap, Abc_NtkObjNumMax(pNtk) );
	vClass = vObjs;

	vList = Abc_NtkFinCreateList( vMap, vClass );
	
   // vClasses = Abc_NtkDetectObjClasses( pNtk, vObjs, &vCoSets );
	
    // refine classes
    vCiSet   = Vec_IntAlloc( 1000 );
    vNodeSet = Vec_IntAlloc( 1000 );
    vMap2    = Vec_WecStart( Abc_NtkObjNumMax(pNtk) );
    vResult  = Vec_WecAlloc( 1000 );
	vCoSet   = Vec_IntAlloc( 1000 );
   // Vec_WecForEachLevel( vClasses, vClass, i )
   {
        // extract one window
       // vCoSet = Vec_WecEntry( vCoSets, i );
		Abc_NtkForEachCo( pNtk, pObj, i )
			Vec_IntPush( vCoSet, Abc_ObjId(pObj) );
        Abc_NtkFinMiterCollect( pNtk, vCoSet, vCiSet, vNodeSet );
		
        // refine one class
       // vList = Abc_NtkFinCreateList( vMap, vClass );
        nCalls = Abc_NtkFinRefinement( pNtk, pNtkFaults, nFaultNum,vClassesSeq, vTypes, vCoSet, vCiSet, vNodeSet, vPairs, vList, vMap2, vResult, fSeq );
        if ( fVerbose )
            printf( "Group %4d :  Obj =%4d. Fins =%4d.  CI =%5d. CO =%5d. Node =%6d.  SAT calls =%5d.\n", 
                i, Vec_IntSize(vClass), Vec_IntSize(vList), Vec_IntSize(vCiSet), Vec_IntSize(vCoSet), Vec_IntSize(vNodeSet), nCalls );
        Vec_IntFree( vList );
    }
    // sort entries in each array
    Vec_WecForEachLevel( vResult, vClass, i )
        Vec_IntSort( vClass, 0 );
    // sort by the index of the first entry
    Vec_WecSortByFirstInt( vResult, 0 ); 
    // cleanup
    Vec_IntFreeP( & vTypes );
    Vec_IntFree( vObjs );
   // Vec_WecFree( vClasses );
    Vec_WecFree( vMap );
    Vec_WecFree( vMap2 );
    //Vec_WecFree( vCoSets );
	Vec_IntFree( vCoSet );
    Vec_IntFree( vCiSet );
    Vec_IntFree( vNodeSet );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Print results.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintFinResults( Vec_Wec_t * vClasses ,char * pFileName  )
{
    Vec_Int_t * vClass;
    int i, k, Entry;
	
	FILE * pFile = fopen( pFileName, "wb" );
	
    Vec_WecForEachLevel( vClasses, vClass, i )
	{
        Vec_IntForEachEntryStart( vClass, Entry, k, 1 )
            //printf( "%d %d\n", Vec_IntEntry(vClass, 0), Entry );
			fprintf(pFile, "%d %d\n", Vec_IntEntry(vClass, 0), Entry );
			//fprintf(pF, "%d %d\n", Vec_IntEntry(vClass, 0), Entry );
	
	}
	fclose(pFile);
}


/**Function*************************************************************

  Synopsis    [Top-level procedure.]

  Description [A. Q. Dao, M. P.-H. Lin, and A. Mishchenko, "SAT-based sequential fault equivalence identification in functional safety verification", Proc. IWLS'20.
	Command : faultclasses -s circuitInput faultfile.txt;]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Abc_NtkDetectClassesTest1(  char * pFileNames[2], int fSeq, int fVerbose, int fVeryVerbose )
{
	 Abc_Ntk_t * pNtk;

	 pNtk = Io_Read( pFileNames[0], IO_FILE_BENCH, 1, 0 );
	
    abctime clk = Abc_Clock();
	fSeq = Abc_NtkDesignType(pFileNames[0]);
	
	Abc_Ntk_t ** pNtkFaults = NULL;
	struct Abc_Ntk_FaultDescr *fault = NULL;
	struct Abc_NtkCircuit * circ = NULL;
	struct Abc_NtkCircuit **fcirc = NULL;
	int maxNode;
	int nFaultNum = 0;
	int i;
	Vec_IntFreeP( &pNtk->vFins );
	pNtk->vFins =  Io_ReadFins(  pNtk, pFileNames[1], fVerbose );
	Abc_Ntk_t **  pNtkF = NULL;
	
	Vec_Wec_t * vClassesSeq = NULL;
	if ( fSeq )
	{
		Abc_NtkReadFaultInf(pFileNames[1], &fault, &nFaultNum);
		circ = Abc_NtkReadInitialCircuit(pFileNames[0]);
		maxNode = Abc_NtkObjNumMax(pNtk);
		pNtkF = (Abc_Ntk_t**) malloc(nFaultNum * sizeof(Abc_Ntk_t *));
		fcirc = calloc(nFaultNum, sizeof(struct Abc_NtkCircuit *));
		for (i = 0; i < nFaultNum; i++) {
			fcirc[i] = Abc_NtkInjectFault(circ, fault[i], maxNode+1);
			pNtkF[i] = Abc_NtkInjectFlt(pNtk, fault[i], maxNode+1);
		}
			
		pNtkFaults = Abc_NtkGenerateAllCircuitsArray(fcirc, nFaultNum);
		vClassesSeq = Abc_NtkDetectFinClassesSeq(pNtkFaults, nFaultNum);

	}

	Vec_Wec_t * vResult;
	vResult = Abc_NtkDetectFinClasses1( pNtk,pNtkFaults,nFaultNum,vClassesSeq,  fVerbose, fSeq );
	printf( "Computed %d equivalence classes with %d item pairs.  ", Vec_WecSize(vResult), Abc_NtkFinCountPairs(vResult) );
	Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
	if ( fVeryVerbose )
		Vec_WecPrint( vResult, 1 );
	char * pFileName = "identical_fault_pairs.txt";
	Abc_NtkPrintFinResults( vResult, pFileName );
	Vec_WecFree( vResult );
	

	if (fSeq)
	{
	Abc_NtkFreeCircuit(circ);
	for (i = 0; i < nFaultNum; i++) {
		Abc_NtkFreeCircuit(fcirc[i]);
		Abc_NtkDelete(pNtkF[i]);
	}

	
	free(fcirc);
	free(fault);
	Abc_NtkFreeCircuits(pNtkFaults, nFaultNum);
	}
}

/**Function*************************************************************

  Synopsis    [Top-level procedure.]

  Description [https://people.eecs.berkeley.edu/~alanmi/publications/2018/tcad18_fault.pdf
				Command : faultclasses circuitInput faultfile.txt;]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/


Vec_Wec_t * Abc_NtkDetectFinClasses( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Int_t * vTypes = NULL; // gate types
    Vec_Int_t * vPairs;        // original info as a set of pairs (ObjId, TypeId)
    Vec_Int_t * vObjs;         // all those objects that have some fin 
    Vec_Wec_t * vMap;          // for each object, the set of fins
    Vec_Wec_t * vMap2;         // for each local object, the set of pairs (Info, Index)
    Vec_Wec_t * vClasses;      // classes of objects
    Vec_Wec_t * vCoSets;       // corresponding CO sets
    Vec_Int_t * vClass;        // one class
    Vec_Int_t * vCoSet;        // one set of COs
    Vec_Int_t * vCiSet;        // one set of CIs
    Vec_Int_t * vNodeSet;      // one set of nodes
    Vec_Int_t * vList;         // one info list
    Vec_Wec_t * vResult;       // resulting equivalences
    int i, iObj, nCalls;
    if ( pNtk->vFins == NULL )
    {
        printf( "Current network does not have the required info.\n" );
        return NULL;
    }
    assert( Abc_NtkIsSopLogic(pNtk) || Abc_NtkIsMappedLogic(pNtk) );
    if ( Abc_NtkIsSopLogic(pNtk) )
    {
        iObj = Abc_NtkFinCheckTypesOk(pNtk);
        if ( iObj )
        {
            printf( "Current network contains unsupported gate types (for example, see node \"%s\").\n", Abc_ObjName(Abc_NtkObj(pNtk, iObj)) );
            return NULL;
        }
        vTypes   = Abc_NtkFinComputeTypes( pNtk );

    }
    else if ( Abc_NtkIsMappedLogic(pNtk) )
    {
        iObj = Abc_NtkFinCheckTypesOk2(pNtk);
        if ( iObj )
        {
            printf( "Current network has mismatch between mapped gate size and fault gate size (for example, see node \"%s\").\n", Abc_ObjName(Abc_NtkObj(pNtk, iObj)) );
            return NULL;
        }
    }
    else assert( 0 );
  
    // collect data
    vPairs   = pNtk->vFins;
    vObjs    = Abc_NtkFinComputeObjects( vPairs, &vMap, Abc_NtkObjNumMax(pNtk) );
	
    vClasses = Abc_NtkDetectObjClasses( pNtk, vObjs, &vCoSets );
	
    // refine classes
    vCiSet   = Vec_IntAlloc( 1000 );
    vNodeSet = Vec_IntAlloc( 1000 );
    vMap2    = Vec_WecStart( Abc_NtkObjNumMax(pNtk) );
    vResult  = Vec_WecAlloc( 1000 );
    Vec_WecForEachLevel( vClasses, vClass, i )
    {
        // extract one window
        vCoSet = Vec_WecEntry( vCoSets, i );
        Abc_NtkFinMiterCollect( pNtk, vCoSet, vCiSet, vNodeSet );
        // refine one class
        vList = Abc_NtkFinCreateList( vMap, vClass ); // vector of ID faults in fault list
        nCalls = Abc_NtkFinRefinement( pNtk,NULL,0,NULL, vTypes, vCoSet, vCiSet, vNodeSet, vPairs, vList, vMap2, vResult,0 );
        if ( fVerbose )
            printf( "Group %4d :  Obj =%4d. Fins =%4d.  CI =%5d. CO =%5d. Node =%6d.  SAT calls =%5d.\n", 
                i, Vec_IntSize(vClass), Vec_IntSize(vList), Vec_IntSize(vCiSet), Vec_IntSize(vCoSet), Vec_IntSize(vNodeSet), nCalls );
        Vec_IntFree( vList );
    }
    // sort entries in each array
    Vec_WecForEachLevel( vResult, vClass, i )
        Vec_IntSort( vClass, 0 );
    // sort by the index of the first entry
    Vec_WecSortByFirstInt( vResult, 0 ); 
    // cleanup
    Vec_IntFreeP( & vTypes );
    Vec_IntFree( vObjs );
    Vec_WecFree( vClasses );
    Vec_WecFree( vMap );
    Vec_WecFree( vMap2 );
    Vec_WecFree( vCoSets );
    Vec_IntFree( vCiSet );
    Vec_IntFree( vNodeSet );
    return vResult;
}



void Abc_NtkDetectClassesTest(  char * pFileNames[2], int fSeq, int fVerbose, int fVeryVerbose)
{
    Abc_Ntk_t * pNtk;
	pNtk = Io_Read( pFileNames[0], IO_FILE_BENCH, 1, 0 );
	 Vec_IntFreeP( &pNtk->vFins );
	pNtk->vFins =  Io_ReadFins(  pNtk, pFileNames[1], fVerbose );
	Vec_Wec_t * vResult;
    abctime clk = Abc_Clock();
  //  if ( fSeq ) 
     //   Abc_NtkFrameExtend( pNtk );
	
    vResult = Abc_NtkDetectFinClasses( pNtk, fVerbose );
    printf( "Computed %d equivalence classes with %d item pairs.  ", Vec_WecSize(vResult), Abc_NtkFinCountPairs(vResult) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    if ( fVeryVerbose )
        Vec_WecPrint( vResult, 1 );
//    if ( fVerbose )
//        Abc_NtkPrintFinResults( vResult );
    Vec_WecFree( vResult );
}

/**Function*************************************************************

  Synopsis    [Top-level procedure.]

  Description [ This function for detecting equivelance faults based on our generat faultlist on technology mapping
				Command: read_bench circuitInput; read_genlib mcnc.genlib ; attach; read_fins faultgenrationfile.txt; faultclassesg;]
               To generate the fault list: read_bench circuitInput; read_genlib mcnc.genlib ; attach; faultclasses -gc;
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Abc_NtkDetectClassesTestGF( Abc_Ntk_t * pNtk, int fVerbose, int fVeryVerbose )
{
    Vec_Wec_t * vResult;
    abctime clk = Abc_Clock();
    vResult = Abc_NtkDetectFinClasses( pNtk, fVerbose );
    printf( "Computed %d equivalence classes with %d item pairs.  ", Vec_WecSize(vResult), Abc_NtkFinCountPairs(vResult) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    if ( fVeryVerbose )
        Vec_WecPrint( vResult, 1 );
//    if ( fVerbose )
//        Abc_NtkPrintFinResults( vResult );
    Vec_WecFree( vResult );
}
////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

