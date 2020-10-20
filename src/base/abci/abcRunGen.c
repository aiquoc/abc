/**CFile****************************************************************

  FileName    [abcRunGen.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface to experimental procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRunGen.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "opt/dau/dau.h"
#include "misc/util/utilTruth.h"
#include "bool/kit/kit.h"
#include "opt/fxu/fxu.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_NktGen_t_ Abc_NktGen_t;
struct Abc_NktGen_t_
{
    int      nPats;        // the number of simulation patterns
    int      nWords;       // the number of machine words of data
    int      nInputs;      // the number of primary inputs
    int      nOutputs;     // the number of primary outputs 
    char **  pInOutNames;  // input/output names
    word *   pSimInfo;     // simulation information
	char **  pPlas0;		//Programing Logic Arrays Off-Set (f = 1)
	char **  pPlas1;		//Programing Logic Arrays On-Set (f = 0 )
	Vec_Ptr_t *	vSuppFun;  // functional supports
	Vec_Ptr_t * vSim0;		// simulation info 1
	Vec_Ptr_t * vSim1;	   // simulation info 2
};

// reading all simulation patterns for inputs/outputs
static inline word * Abc_GenSimIn ( Abc_NktGen_t * p, int i )            { return p->pSimInfo + p->nWords * i;                                  }
static inline word * Abc_GenSimOut( Abc_NktGen_t * p, int i )            { return p->pSimInfo + p->nWords * (i + p->nInputs);                   }

// reading one simulation value for inputs/outputs 
static inline int    Abc_GenGetInfoIn ( Abc_NktGen_t * p, int i, int k ) { assert(k < p->nPats); return Abc_TtGetBit( Abc_GenSimIn (p, i), k ); }
static inline int    Abc_GenGetInfoOut( Abc_NktGen_t * p, int i, int k ) { assert(k < p->nPats); return Abc_TtGetBit( Abc_GenSimOut(p, i), k ); }

// setting one simulation value for inputs/outputs 
static inline void   Abc_GenSetInfoIn ( Abc_NktGen_t * p, int i, int k ) { assert(k < p->nPats); Abc_TtSetBit( Abc_GenSimIn (p, i), k );        }
static inline void   Abc_GenSetInfoOut( Abc_NktGen_t * p, int i, int k ) { assert(k < p->nPats); Abc_TtSetBit( Abc_GenSimOut(p, i), k );        }

// cleaning simulation values for inputs/outputs
static inline void   Abc_GenCleanSimIn ( Abc_NktGen_t * p, int i )       { assert(i < p->nInputs);  memset( Abc_GenSimIn(p, i),  0, sizeof(word)*p->nWords );   }
static inline void   Abc_GenCleanSimOut( Abc_NktGen_t * p, int i )       { assert(i < p->nOutputs); memset( Abc_GenSimOut(p, i), 0, sizeof(word)*p->nWords );   }

// filling with ones or flopping simulation values for one input
static inline void   Abc_GenFillSimIn ( Abc_NktGen_t * p, int i )        { memset( Abc_GenSimIn(p, i),  0xF, sizeof(word)*p->nWords );          }
static inline void   Abc_GenFlipSimIn ( Abc_NktGen_t * p, int i )        { Abc_TtNot( Abc_GenSimIn(p, i), p->nWords );                          }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates data-tructure to store input/output simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_NktGen_t * Abc_NtkGenAlloc( char * pFileName, int nPats )
{
    Abc_NktGen_t * p;
    char * pStr, Buffer[10000]; int i, nIns, nOuts;
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return 0;
    }
    // get input/output count
    if ( 2 != fscanf( pFile, "%d %d", &nIns, &nOuts ) )
    {
        printf( "Cannot read input paramete from file \"%s\".\n", pFileName );
        return 0;
    }
    // alloc memory
    p = ABC_CALLOC( Abc_NktGen_t, 1 );
	if ((nIns>31) || (1<<nIns > nPats))
		p->nPats = nPats;
	else
		p->nPats = 1<<nIns;
    //p->nPats    = (nPats>>>(1<<nIns);
	printf("nPats = %d \n", p->nPats);
    p->nWords   = Abc_Bit6WordNum(2*nPats);
    p->nInputs  = nIns;
	//printf("The number of inputs = %d \n", p->nInputs);
	//printf("The number real test pattern = %d \n", 1 << p->nInputs);
    p->nOutputs = nOuts;
    // collect names
    p->pInOutNames = ABC_ALLOC( char *, p->nInputs + p->nOutputs );
    pStr = fgets( Buffer, 10000, pFile );
    pStr = fgets( Buffer, 10000, pFile );
    p->pInOutNames[0] = Abc_UtilStrsav(strtok(Buffer, " "));
    for ( i = 1; i < p->nInputs + p->nOutputs; i++ )
        p->pInOutNames[i] = Abc_UtilStrsav(strtok(NULL, " \n"));
    // create sim info
    p->pSimInfo = ABC_CALLOC( word, p->nWords * (p->nInputs + p->nOutputs) );
    return p;
}
void Abc_NtkGenFree( Abc_NktGen_t * p )
{
    int i;
    for ( i = 0; i < p->nInputs + p->nOutputs; i++ )
        ABC_FREE(p->pInOutNames[i]);
    ABC_FREE(p->pInOutNames);
    ABC_FREE(p->pSimInfo);
	for ( i = 0; i < p->nOutputs; i ++)
		ABC_FREE(p->pPlas1[i]);
	ABC_FREE(p->pPlas1);
	for ( i = 0; i < p->nOutputs; i ++)
		ABC_FREE(p->pPlas0[i]);
	ABC_FREE(p->pPlas0);

    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Fill out with random simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkGenFillTruthTables( Abc_NktGen_t * p )
{
    int i, w, nVar = Abc_Base2Log( 32*p->nWords );
    for ( i = 0; i < p->nInputs; i++ )
        for ( w = 0; w < p->nWords; w++ )
            Abc_TtIthVar( Abc_GenSimIn(p, i), i, nVar);
}
void Abc_NtkGenFillRandom( Abc_NktGen_t * p )
{
    int i, w;
    for ( i = 0; i < p->nInputs; i++ )
        for ( w = 0; w < p->nWords; w++ )
            Abc_GenSimIn(p, i)[w] = Gia_ManRandomW(0);
}
int addSimLinePLA0(char **p, char *inBuf, int nIn)
{
	char *p_new;
	int i, p_ln;
	if(*p==NULL)
	{
		p_ln = 0;
		p_new = (char*)malloc((p_ln + nIn + 3 + 1)*sizeof(char));
	}
	else
	{
		p_ln = strlen(*p);
		p_new = (char*)realloc(*p, (p_ln + nIn + 3 + 1)*sizeof(char));
	}
	//p_ln = (*p==NULL)?0:strlen(*p);
	//p_new = (char*)realloc(*p, (p_ln + nIn + 3 + 1)*sizeof(char));
	if(p_new == NULL)
	{
		printf("Can't realocate in addSimLinePLA\n");
		return 0;
	}
	// write input
	for(i=0 ; i < nIn; i++)
	{
		p_new[p_ln + i] = inBuf[i*2];
	}
	p_ln = p_ln + nIn;
	// write 3 last characters " 0\n" + NULL
	p_new[p_ln + 0] = ' ';
	p_new[p_ln + 1] = '0';
	p_new[p_ln + 2] = '\n';
	p_new[p_ln + 3] = 0;
	*p = p_new;
	return 1;
}
int addSimLinePLA1(char **p, char *inBuf, int nIn)
{
	char *p_new;
	int i, p_ln;
	if(*p==NULL)
	{
		p_ln = 0;
		p_new = (char*)malloc((p_ln + nIn + 3 + 1)*sizeof(char));
	}
	else
	{
		p_ln = strlen(*p);
		p_new = (char*)realloc(*p, (p_ln + nIn + 3 + 1)*sizeof(char));
	}
	//p_ln = (*p==NULL)?0:strlen(*p);
	//p_new = (char*)realloc(*p, (p_ln + nIn + 3 + 1)*sizeof(char));
	if(p_new == NULL)
	{
		printf("Can't realocate in addSimLinePLA\n");
		return 0;
	}
	// write input
	for(i=0 ; i < nIn; i++)
	{
		p_new[p_ln + i] = inBuf[i*2];
	}
	p_ln = p_ln + nIn;
	// write 3 last characters " 1\n" + NULL
	p_new[p_ln + 0] = ' ';
	p_new[p_ln + 1] = '1';
	p_new[p_ln + 2] = '\n';
	p_new[p_ln + 3] = 0;
	*p = p_new;
	return 1;
}

/**Function*************************************************************

  Synopsis    [Simulate one batch of input patterns through iogen.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGenSimulate( Abc_NktGen_t * p, char * pFileIoGen )
{
    int i, k, nIns, nOuts, nLines;
    char * pStr, Command[5000], Buffer[10000];
    char * pFileNameIn  = "input.txt";
    char * pFileNameOut = "output.txt";
	p->pPlas0 = ABC_ALLOC( char *, p->nOutputs );
	p->pPlas1 = ABC_ALLOC( char *, p->nOutputs );

    // create input files
    FILE * pFile = fopen( pFileNameIn, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileNameIn );
        return 0;
    }
    fprintf( pFile, "%d %d\n", p->nInputs, p->nPats);
    fprintf( pFile, "%s", p->pInOutNames[0] );
	printf("The number of real test patterns %d \n", (1 << p->nInputs));
    for ( i = 1; i < p->nInputs; i++ )
		fprintf( pFile, " %s", p->pInOutNames[i] );
    fprintf( pFile, "\n" );
	/* for ( k = 0; k < p->nPats; k++ )
    {
        fprintf( pFile, "%d", Abc_GenGetInfoIn(p, 0, k) );
        for ( i = 1; i < p->nInputs; i++ )
            fprintf( pFile, " %d", Abc_GenGetInfoIn(p, i, k) );
        fprintf( pFile, "\n" );
    }
    fclose( pFile );*/
	 //int beginIn = 2;
	 int count;
	 if(p->nInputs%10==0){
	 count=(p->nInputs/10);
	 }
	 else{
		 count=(p->nInputs/10)+1;
	 }
	
	for ( k = 0; k < p->nPats; k++ )
    {
		//if(beginIn>1)
			//fprintf( pFile, "%d", 0 );
		for(int m=0;m<count;m++){
			if(m==0){
				fprintf( pFile, "%d", Abc_GenGetInfoIn(p, 0, k) );
			}
			else{
				fprintf( pFile, " %d", Abc_GenGetInfoIn(p, 0, k) );
			}
		//for(i=0;i<beginIn;i++)
			//fprintf( pFile, " %d", 0);
		//for (i=1;i<(p->nInputs-beginIn );i++)
		if(m!=count-1){
			for ( i = 1; i < 10; i++ )
				fprintf( pFile, " %d", Abc_GenGetInfoIn(p, i, k) );
		}
		else{
			for ( i = 1; i < p->nInputs-(10*(count-1)); i++ )
				fprintf( pFile, " %d", Abc_GenGetInfoIn(p, i, k) );
		}	
		}
		fprintf( pFile, "\n" );
    }
    fclose( pFile );
	
	for (k = 0; k < p->nOutputs; k++)
	{
		p->pPlas0[k] = 0;
		p->pPlas1[k] = 0;
	}
    // run iogen
    sprintf( Command, "%s %s %s", pFileIoGen, pFileNameIn, pFileNameOut );
    if ( system(Command) == -1 )
    {
        printf( "Failed to run simulation binary \"%s\".\n", pFileIoGen );
        return 0;
    }
    // read output files
    pFile = fopen( pFileNameOut, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileNameOut );
        return 0;
    }
    // read parameters
    if ( 3 != fscanf( pFile, "%d %d %d", &nIns, &nOuts, &nLines ) )
    {
        printf( "Cannot correctly read the number of inputs/outputs/lines.\n" );
        fclose( pFile );
        return 0;
    }
   // if ( nIns != p->nInputs || nOuts != p->nOutputs || nLines != p->nPats )
    if ( nIns != p->nInputs || nOuts != p->nOutputs  )
    {
        printf( "The resulting file does not have matching parameters.\n" );
        fclose( pFile );
        return 0;
    }
    // skip parameters and names
    pStr = fgets( Buffer, 10000, pFile );
    pStr = fgets( Buffer, 10000, pFile );
    // read simulation info
    for ( i = 0; i < p->nOutputs; i++ )
        Abc_GenCleanSimOut( p, i );
    for ( k = 0; k < p->nPats; k++ )
    {
        if ( fgets( Buffer, 10000, pFile ) == NULL )
        {
            printf( "Cannot read patterns from file \"%s\".\n", pFileNameOut );
            fclose( pFile );
            return 0;
        }
        for ( i = 0; i < p->nOutputs; i++ )
		{
            if ( Buffer[2*(p->nInputs+i)] == '1' )
			  Abc_GenSetInfoOut(p,i,k);
		}
		 for ( i = 0; i < p->nOutputs; i++ )
		{
            if ( Buffer[2*(p->nInputs+i)] == '1' )
              addSimLinePLA1(&p->pPlas1[i], Buffer, p->nInputs);
		    if ( Buffer[2*(p->nInputs+i)] == '0' )
              addSimLinePLA0(&p->pPlas0[i], Buffer, p->nInputs);	
		}
    }
    fclose( pFile );
	
	// Display simulation pPlas on-set
   /* printf("Print:\n");
    for(k=0; k< p->nOutputs;k++)
    {
    	printf("PLA output %d:\n",k);
    	printf("%s",p->pPlas1[k]);
		printf("%s",p->pPlas0[k]);
    }*/
	
    printf( "Finished simulation.\n" );
    return 1;
}


int Abc_NtkGenSimulateDivide( Abc_NktGen_t * p, char * pFileIoGen, int nLoop )
{
    int i, k, nIns, nOuts, nLines;
    char * pStr, Command[5000], Buffer[10000];
	char snum[30];
	char pFileNameIn[100]="input";
	char pFileNameOut[100]="output";
	sprintf(snum,"%d",nLoop);
	strcat(pFileNameIn,snum);
	strcat(pFileNameIn,".txt");
	strcat(pFileNameOut,snum);
	strcat(pFileNameOut,".txt");
    // create input files
    FILE * pFile = fopen( pFileNameIn, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileNameIn );
        return 0;
    }
    fprintf( pFile, "%d %d\n", p->nInputs, p->nPats);
    fprintf( pFile, "%s", p->pInOutNames[0] );  	
    for ( i = 1; i < p->nInputs; i++ )
		fprintf( pFile, " %s", p->pInOutNames[i] );
    fprintf( pFile, "\n" );

	 int count;
	 if(p->nInputs%10==0){
	 count=(p->nInputs/10);
	 }
	 else{
		 count=(p->nInputs/10)+1;
	 }
	
	for ( k = 0; k < p->nPats; k++ )
    {
		for(int m=0;m<count;m++){
			
			if(m==0){
				if(m==nLoop){
					fprintf( pFile, "%d", Abc_GenGetInfoIn(p, 0, k) );
				}
				else{
					fprintf( pFile,"0");
				}
			}
			else{
				if(m==nLoop){
					fprintf( pFile, " %d", Abc_GenGetInfoIn(p, 0, k) );
				}
				else{
					fprintf( pFile, " 0");
				}
			}
			if(m!=count-1){
				if(m==nLoop){
					for ( i = 1; i < 10; i++ )
						fprintf( pFile, " %d", Abc_GenGetInfoIn(p, i, k) );
				}
				else{
					for ( i = 1; i < 10; i++ )
						fprintf( pFile, " 0" );
				}
			}
			else{
				if(m==nLoop){
					for ( i = 1; i < p->nInputs-(10*(count-1)); i++ )
						fprintf( pFile, " %d", Abc_GenGetInfoIn(p, i, k) );
				}
				else{
					for ( i = 1; i < p->nInputs-(10*(count-1)); i++ )
						fprintf( pFile, " 0" );
				}
			}			
		}
		fprintf( pFile, "\n" );	
    }
    fclose( pFile );
	
    // run iogen
    sprintf( Command, "%s %s %s", pFileIoGen, pFileNameIn, pFileNameOut );
    if ( system(Command) == -1 )
    {
        printf( "Failed to run simulation binary \"%s\".\n", pFileIoGen );
        return 0;
    }
    // read output files
    pFile = fopen( pFileNameOut, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileNameOut );
        return 0;
    }
    // read parameters
    if ( 3 != fscanf( pFile, "%d %d %d", &nIns, &nOuts, &nLines ) )
    {
        printf( "Cannot correctly read the number of inputs/outputs/lines.\n" );
        fclose( pFile );
        return 0;
    }
   // if ( nIns != p->nInputs || nOuts != p->nOutputs || nLines != p->nPats )
    if ( nIns != p->nInputs || nOuts != p->nOutputs  )
    {
        printf( "The resulting file does not have matching parameters.\n" );
        fclose( pFile );
        return 0;
    }
    // skip parameters and names
    pStr = fgets( Buffer, 10000, pFile );
    pStr = fgets( Buffer, 10000, pFile );
    // read simulation info
    for ( i = 0; i < p->nOutputs; i++ )
        Abc_GenCleanSimOut( p, i );
    for ( k = 0; k < p->nPats; k++ )
    {
        if ( fgets( Buffer, 10000, pFile ) == NULL )
        {
            printf( "Cannot read patterns from file \"%s\".\n", pFileNameOut );
            fclose( pFile );
            return 0;
        }
        for ( i = 0; i < p->nOutputs; i++ )
		{
            if ( Buffer[2*(p->nInputs+i)] == '1' )
			  Abc_GenSetInfoOut(p,i,k);
		}
    }
    fclose( pFile );
	
    printf( "Finished simulation divide.\n" );
    return 1;
}
/**Function*************************************************************

  Synopsis    [Add simulation line PLA/ Test]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Abc_NtkGenLinePLA(void) {

	int i, k, nIns, nOuts, nLines;
    char * pFileNameOut = "output.txt";
    char **pPlas;
    char * pStr;
    char Buffer[5000];
	FILE * pFile = fopen( pFileNameOut, "rb" );
	if ( pFile == NULL )
	{
		printf( "Cannot open file \"%s\" for reading.\n", pFileNameOut );
		return 0;
	}
	// read parameters
	if ( 3 != fscanf( pFile, "%d %d %d", &nIns, &nOuts, &nLines ) )
	{
		printf( "Cannot correctly read the number of inputs/outputs/lines.\n" );
		fclose( pFile );
		return 0;
	}

	printf("In: %d, Out: %d, Line: %d\n",nIns,nOuts,nLines);

	pPlas = malloc(nOuts*sizeof(char*));
	for(k=0;k<nOuts;k++)
	{
		pPlas[k]=NULL;
	}
	// skip parameters and names
	pStr = fgets( Buffer, 10000, pFile );
	pStr = fgets( Buffer, 10000, pFile );
	// read simulation info
    for ( i = 0; i < nLines; i++ )
    {
        if ( fgets( Buffer, 10000, pFile ) == NULL )
        {
            printf( "Cannot read patterns from file \"%s\".\n", pFileNameOut );
            fclose( pFile );
            return 0;
        }
        for ( k = 0; k < nOuts; k++ )
            if ( Buffer[2*(nIns+k)] == '1' )
            	addSimLinePLA1(&pPlas[k], Buffer, nIns);
    }
    fclose( pFile );

    printf( "Finished simulation.\n" );
    // Display simulation pPlas
    printf("Print:\n");
    for(k=0; k<nOuts;k++)
    {
    	printf("PLA output %d:\n",k);
    	printf("%s",pPlas[k]);
    }
    // Free
    for(k=0;k<nOuts;k++)
	{
    	free(pPlas[k]);
	}
    free(pPlas);
	return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkGetInputs( char * pFileName, int * pnInputs, int * pnOutputs )
{
    FILE * pFile = fopen( pFileName, "rb" );
    *pnInputs = *pnOutputs = 0;
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return;
    }
    if ( 2 != fscanf( pFile, "%d %d", pnInputs, pnOutputs ) )
        printf( "Cannot correctly read the number of inputs/outputs.\n" );
}

/**Function*************************************************************

  Synopsis    [Generate the AIGs Off-Set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkGentoOffSetAig(Abc_NktGen_t * p )
{
 //Fxu_Data_t Params, * pa = &Params;
    Abc_Ntk_t * pNtkSop, * pNtkAig; 
    Abc_Obj_t * pNode, * pFanin, * pObj ;
    int i, k;
    // allocate logic network with SOP local functions
    pNtkSop = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    pNtkSop->pName = Extra_FileNameGeneric("Off-Set");
    // create primary inputs/outputs
    for ( i = 0 ; i < p->nInputs; i++ ){
        pObj = Abc_NtkCreatePi( pNtkSop );
		Abc_ObjAssignName(pObj, p->pInOutNames[i], NULL);
	}
    for ( i = 0; i < p->nOutputs; i++ ){
		   pObj = Abc_NtkCreatePo( pNtkSop );	
		Abc_ObjAssignName(pObj, p->pInOutNames[i + p->nInputs], NULL);
	}
    // create internal nodes
    for ( i = 0; i < p->nOutputs; i++ )
    {
			//printf("PLA off-set \n");
			//printf("output %d \n%s \n",i, p->pPlas0[i] );
			//printf("PLA on-set \n");
			//printf("output %d \n%s \n",i, p->pPlas1[i] );
		if (p->pPlas0[i] == NULL){
			pNode = Abc_NtkCreateNodeConst1(pNtkSop);
			Abc_ObjAddFanin( Abc_NtkPo(pNtkSop, i), pNode );
		}
		else
		{			
			pNode = Abc_NtkCreateNode( pNtkSop );
			Abc_NtkForEachPi( pNtkSop, pFanin, k )
				Abc_ObjAddFanin( pNode, pFanin );
			//printf("Testing \n");
			pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtkSop->pManFunc, p->pPlas0[i] );
			//printf("output %d \n %s \n",i, p->pPlas0[i] );
			Abc_ObjAddFanin( Abc_NtkPo(pNtkSop, i), pNode );
			// check that the number of inputs is the same
			assert( Abc_SopGetVarNum((char*)pNode->pData) == p->nInputs );
		}
    }
    if ( !Abc_NtkCheck( pNtkSop ) )
        fprintf( stdout, "Abc_NtkGentoAig(): Network check has failed.\n" );
    Abc_NtkToSop(pNtkSop,-1, ABC_INFINITY);
	// perform fast_extract
   // Abc_NtkSetDefaultFxParams( pa );
    //Abc_NtkFastExtract( pNtkSop, pa );
    //Abc_NtkFxuFreeInfo( pa );
    // convert to an AIG
    pNtkAig = Abc_NtkStrash( pNtkSop, 0, 1, 0 );
    Abc_NtkDelete( pNtkSop );
	Io_WriteBlifLogic( pNtkAig,"tempoff.blif",1);
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Generate the AIGs On-Set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

Abc_Ntk_t * Abc_NtkGentoOnSetAig(Abc_NktGen_t * p )
{
    Abc_Ntk_t * pNtkSop, * pNtkAig; 
    Abc_Obj_t * pNode, * pFanin, * pObj;
    int i, k;
    // allocate logic network with SOP local functions
    pNtkSop = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    pNtkSop->pName = Extra_FileNameGeneric("On-Set");
    // create primary inputs/outputs
    for ( i = 0; i < p->nInputs; i++ ){
        pObj = Abc_NtkCreatePi( pNtkSop );
		Abc_ObjAssignName(pObj, p->pInOutNames[i], NULL);
	}
    for ( i = 0; i < p->nOutputs; i++ ){
		   pObj = Abc_NtkCreatePo( pNtkSop );	
		Abc_ObjAssignName(pObj, p->pInOutNames[i + p->nInputs ], NULL);
	}
    // create internal nodes
    for ( i = 0; i < p->nOutputs; i++ )
    {
        if (p->pPlas1[i] == NULL){
			pNode = Abc_NtkCreateNodeConst0(pNtkSop);
			Abc_ObjAddFanin( Abc_NtkPo(pNtkSop, i), pNode );
		}
		else 
		{
			pNode = Abc_NtkCreateNode( pNtkSop );
			Abc_NtkForEachPi( pNtkSop, pFanin, k )
				Abc_ObjAddFanin( pNode, pFanin );
			//printf("Testing \n");	
			pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtkSop->pManFunc, p->pPlas1[i] );	
				//printf("%s \n",p->pPlas1[i] );
			Abc_ObjAddFanin( Abc_NtkPo(pNtkSop, i), pNode );
			// check that the number of inputs is the same
			assert( Abc_SopGetVarNum((char*)pNode->pData) == p->nInputs );
		}
    }
    if ( !Abc_NtkCheck( pNtkSop ) )
        fprintf( stdout, "Abc_NtkGentoOnSetAig(): Network check has failed.\n" );
	Abc_NtkToSop(pNtkSop,-1, ABC_INFINITY);
    // convert to an AIG
    pNtkAig = Abc_NtkStrash( pNtkSop, 0, 1, 0 );
    Abc_NtkDelete( pNtkSop );
	Io_WriteBlifLogic( pNtkAig,"tempon.blif",1);
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Testing procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkRunGen( char * pFileNames[2], int fVerbose )
{
    Abc_NktGen_t * p;
//	extern Abc_Ntk_t * Abc_NtkCollapseSat( Abc_Ntk_t * pNtk, int nCubeLim, int nBTLimit, int nCostMax, int fCanon, int fReverse, int fCnfShared, int fVerbose );
	//extern Vec_Int_t * Abc_NtkCollectCiSupps( Abc_Ntk_t * pNtk, int fVerbose );
	//void Abc_NtkPrintStrSupports( Abc_Ntk_t * pNtk, int fMatrix );
	//Vec_Ptr_t  * vSupps;
   Abc_Ntk_t * pNtkOn, * pNtkOff, * pNtkClOn, * pNtkClOff; // * pNtkInter;

	int i, nInputs, nOutputs;
    Acb_NtkGetInputs( pFileNames[1], &nInputs, &nOutputs );
/*
    if ( nInputs > 16 )
    {
        printf( "Cannot exhastively simulate more than 16 inputs.\n" );
        return;
    }
    p = Abc_NtkGenAlloc( pFileNames[1], 1 << nInputs );
*/
	//p = Abc_NtkGenAlloc( pFileNames[1], 1 << nInputs );
	p = Abc_NtkGenAlloc( pFileNames[1], 1024);
    if ( p == NULL ) 
        return;
	printf( "Allocated internal data-structure with %d inputs, %d outputs, and %d simulation patterns.\n", p->nInputs, p->nOutputs, p->nPats );

	//Gia_ManRandom(1);
    Abc_NtkGenFillRandom( p );
    Abc_NtkGenFillTruthTables( p );
	if ( !Abc_NtkGenSimulate( p, pFileNames[0] ) )
        return;
	
	// convert to AIG 
	pNtkOn = Abc_NtkGentoOnSetAig(p);
	Abc_NtkPrintStats( pNtkOn, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 );
	//Abc_NtkPrintStrSupports(pNtkOn, 0);
	
	/*pNtkOn = Abc_NtkStrash( pNtkOn, 0, 0, 0 );
	pNtkClOn = Abc_NtkCollapseSat( pNtkOn, 0, 1000000, 20000000, 0, 0, 0, 1 );
	printf("Abc_NtkCollapseSat \n");
	Abc_NtkPrintStrSupports(pNtkClOn, 0);
	Abc_NtkPrintStats( pNtkClOn, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 );*/
	
	/*pNtkOff = Abc_NtkStrash( pNtkOff, 0, 0, 0 );
	pNtkClOff = Abc_NtkCollapseSat( pNtkOff, 0, 1000000, 20000000, 0, 0, 0, 1 );
	printf("Abc_NtkCollapseSat \n");
	Abc_NtkPrintStrSupports(pNtkClOff, 0);
	Abc_NtkPrintStats( pNtkClOff, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 );*/
	
	//Interplates two networks
	/*extern Abc_Ntk_t * Abc_NtkInter( Abc_Ntk_t * pNtkClOn, Abc_Ntk_t * pNtkClOff, int fRelation, int fVerbose );
	pNtkClOn = Abc_NtkStrash( pNtkClOn, 0, 0, 0 );
	pNtkClOff = Abc_NtkStrash( pNtkClOff, 0, 0, 0 );
	pNtkInter = Abc_NtkInter( pNtkClOn, pNtkClOff, 0, 1 );
	printf("Testing ***********\n");
	if (pNtkInter)
		Abc_NtkPrintStats( pNtkInter, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 );*/
	
	
	pNtkOff = Abc_NtkGentoOffSetAig(p);
	Abc_NtkPrintStats( pNtkOff, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 );
	//Abc_NtkPrintStrSupports(pNtkOff, 0);
		
	//int nLoop;
	
	int nInPs[p->nInputs];
	int count;
	Vec_Int_t * vSets;
	vSets = Vec_IntAlloc( 1000 );
	 if(p->nInputs%10==0){
	 count=(p->nInputs/10);
	 }
	 else{
		 count=(p->nInputs/10)+1;
	 }
	 for(int m=0; m < count; m++){
		 printf("The input divide loop %d \n", m);
		 if ( !Abc_NtkGenSimulateDivide( p, pFileNames[0] , m ))
        return;
		if(m!=count-1){
			for ( i = 0; i < p->nOutputs; i++ )
			{
				printf( "Output %2d : ", i );
				//extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
				//int nVarReal= Dau_DsdMinBase(pTruth, nVars, nInPs);
				Dau_DsdPrintFromTruth( Abc_GenSimOut(p, i), 10 );
				printf( "\n" );
				//extern Abc_Ntk_t * Abc_NtkDecFromTruth( word * pTruth, int nVars, int nLutSize );
				//Abc_Ntk_t * pNtkAig;
				//pNtkAig = Abc_NtkDecFromTruth( Abc_GenSimOut(p, i), 10, 4 );
				//Abc_NtkPrintStats( pNtkAig, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 );
				//extern Kit_DsdNtk_t * Kit_DsdDecompose( unsigned * pTruth, int nVars );
				//Kit_DsdNtk_t * pNtk;
				//pNtk = Kit_DsdDecompose( Abc_GenSimOut(p, i), 10 );
				//Kit_DsdPrint( stdout, pNtk );
				//printf( "\n" );
				//extern unsigned Lpk_ComputeSets( Kit_DsdNtk_t * p, Vec_Int_t * vSets );
				//Lpk_ComputeSets(pNtk, vSets);
				//extern  void Lpk_PrintSets( Vec_Int_t * vSets );
				//Lpk_PrintSets(vSets);
				//Kit_DsdNtkFree( pNtk );
				
				//Abc_TtPrintBinary((unsigned *)Abc_GenSimOut(p, i), 6 );
			}
		}
		else{
			for ( i = 0; i < p->nOutputs; i++ ){
				printf( "Output %2d : ", i );
				extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
				Kit_DsdPrintFromTruth( Abc_GenSimOut(p, i), p->nInputs-(10*(count-1)) );
				printf( "\n" );
				/*extern Kit_DsdNtk_t * Kit_DsdDecompose( unsigned * pTruth, int nVars );
				Kit_DsdNtk_t * pNtk;
				pNtk = Kit_DsdDecompose( Abc_GenSimOut(p, i), p->nInputs-(10*(count-1)) );
				Kit_DsdPrint( stdout, pNtk );
				printf( "\n" );
				Kit_DsdNtkFree( pNtk );*/
			}
		}
	 }
	 
	
	//extern Vec_Int_t * Dau_DecFindSets( word * pInit, int nVars );
	//extern void Dau_DecPrintSets( Vec_Int_t * vSets, int nVars );
	//vSets = Dau_DecFindSets ((unsigned *)Abc_GenSimOut(p, i), p->nInputs);
	//Dau_DecPrintSets(vSets,p->nInputs);
	//Vec_IntPrint(vSets);
	
	//find the support variable
	/*printf( "The support variable are:\n" );
	for ( i = 0; i < p->nOutputs; i++ ){
		printf( "Output %2d : ", i );
		unsigned uSupp;
		extern unsigned Kit_TruthSupport( unsigned * pTruth, int nVars );
		uSupp = Kit_TruthSupport( Abc_GenSimOut(p, i), p->nInputs );
		Extra_PrintBinary( stdout, &uSupp, p->nInputs ); printf( "\n" );
	}
	
    // print the resulting functions
	printf( "The iogen functions are:\n" );
    for ( i = 0; i < p->nOutputs; i++ )
    {
         printf( "Output %2d : ", i );
		extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
		Kit_DsdPrintFromTruth( Abc_GenSimOut(p, i), p->nInputs );
		printf( "\n" );
		Abc_TtPrintBinary((unsigned *)Abc_GenSimOut(p, i), p->nInputs );
    }

	//pNtk = Abc_NtkCreateWithNode( pSopCover );*/
	printf( "Finished printout.\n" );
   // fflush( stdout );
    // cleanup
    Abc_NtkGenFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

