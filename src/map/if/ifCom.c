/**CFile****************************************************************

  FileName    [ifCom.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Command handlers.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifCom.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "base/main/main.h"
#include "base/io/ioAbc.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int If_CommandReadLut ( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandPrintLut( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandReadCell( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandPrintCell( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandReadBox ( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandPrintBox( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandWriteBox( Abc_Frame_t * pAbc, int argc, char **argv );
//static int If_CommandGenBox  ( Abc_Frame_t * pAbc, int argc, char **argv );
//static int If_CommandPatchBox( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandGenDesignBoxes( Abc_Frame_t * pAbc, int argc, char **argv );
//static int If_CommandBuildTim( Abc_Frame_t * pAbc, int argc, char **argv );
static int If_CommandPrintTim( Abc_Frame_t * pAbc, int argc, char **argv );

static int If_ParseDelayValue( char * pDelay, int Scale, int * pValue )
{
    char * pEnd;
    double Value;
    if ( pDelay[0] == '-' && pDelay[1] == 0 )
    {
        *pValue = -ABC_INFINITY;
        return 1;
    }
    Value = strtod( pDelay, &pEnd );
    if ( pEnd == pDelay || *pEnd != 0 )
        return 0;
    *pValue = (int)( Value * Scale + 0.5 );
    return 1;
}

static int If_FindPiIndex( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pTemp;
    int i;
    Abc_NtkForEachPi( pNtk, pTemp, i )
        if ( pTemp == pObj )
            return i;
    return -1;
}

static int If_FindPoIndex( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pTemp;
    int i;
    Abc_NtkForEachPo( pNtk, pTemp, i )
        if ( pTemp == pObj )
            return i;
    return -1;
}

static Abc_Obj_t * If_FindNetPo( Abc_Obj_t * pNet )
{
    Abc_Obj_t * pFanout;
    int i;
    if ( pNet == NULL )
        return NULL;
    Abc_ObjForEachFanout( pNet, pFanout, i )
        if ( Abc_ObjIsPo(pFanout) )
            return pFanout;
    return NULL;
}

static char * If_BoxInstanceName( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pModel = NULL;
    if ( Abc_ObjIsBlackbox(pObj) && Abc_ObjData(pObj) != NULL )
        pModel = (Abc_Ntk_t *)Abc_ObjData(pObj);
    return pModel ? Abc_NtkName(pModel) : Abc_ObjName(pObj);
}

static Abc_Obj_t * If_CreatePiNamed( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet = Abc_NtkFindOrCreateNet( pNtk, pName );
    Abc_Obj_t * pPi  = Abc_NtkCreatePi( pNtk );
    Abc_ObjAddFanin( pNet, pPi );
    return pPi;
}

static Abc_Obj_t * If_CreatePoNamed( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet = Abc_NtkFindOrCreateNet( pNtk, pName );
    Abc_Obj_t * pPo  = Abc_NtkCreatePo( pNtk );
    Abc_ObjAddFanin( pPo, pNet );
    return pPo;
}

static Abc_Ntk_t * If_CreateBlackboxModel( char * pName, char ** pInputs, int nInputs, char ** pOutputs, int nOutputs )
{
    Abc_Ntk_t * pNtk;
    int i;
    pNtk = Abc_NtkAlloc( ABC_NTK_NETLIST, ABC_FUNC_BLACKBOX, 1 );
    pNtk->pName = Abc_UtilStrsav( pName );
    for ( i = 0; i < nInputs; i++ )
        If_CreatePiNamed( pNtk, pInputs[i] );
    for ( i = 0; i < nOutputs; i++ )
        If_CreatePoNamed( pNtk, pOutputs[i] );
    return pNtk;
}

static Abc_Ntk_t * If_CreateWhiteboxBypassModel( char * pName, char * pInput, char * pOutput )
{
    Abc_Ntk_t * pNtk;
    pNtk = Abc_NtkAlloc( ABC_NTK_NETLIST, ABC_FUNC_SOP, 1 );
    pNtk->pName = Abc_UtilStrsav( pName );
    Io_ReadCreatePi( pNtk, pInput );
    Io_ReadCreatePo( pNtk, pOutput );
    Io_ReadCreateBuf( pNtk, pInput, pOutput );
    return pNtk;
}

static Abc_Ntk_t * If_CreateWhiteboxFlopModel( char * pName, char * pDataIn, char * pClock, char * pDataOut )
{
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pLatch;
    pNtk = Abc_NtkAlloc( ABC_NTK_NETLIST, ABC_FUNC_SOP, 1 );
    pNtk->pName = Abc_UtilStrsav( pName );
    Io_ReadCreatePi( pNtk, pDataIn );
    Io_ReadCreatePi( pNtk, pClock );
    Io_ReadCreatePo( pNtk, pDataOut );
    pLatch = Io_ReadCreateLatch( pNtk, pDataIn, pDataOut );
    Abc_LatchSetInit0( pLatch );
    return pNtk;
}

static Abc_Obj_t * If_CreateBlackboxInstance( Abc_Ntk_t * pTop, Abc_Ntk_t * pModel, char * pInstName, char ** pInputs, char ** pOutputs )
{
    Abc_Obj_t * pBox, * pTerm, * pNet;
    int i;
    pBox = Abc_NtkCreateBlackbox( pTop );
    Abc_ObjAssignName( pBox, pInstName, NULL );
    Abc_ObjSetData( pBox, pModel );
    Abc_NtkForEachPi( pModel, pTerm, i )
    {
        Abc_Obj_t * pBi = Abc_NtkCreateBi( pTop );
        pNet = Abc_NtkFindOrCreateNet( pTop, pInputs[i] );
        Abc_ObjAddFanin( pBi, pNet );
        Abc_ObjAddFanin( pBox, pBi );
    }
    Abc_NtkForEachPo( pModel, pTerm, i )
    {
        Abc_Obj_t * pBo = Abc_NtkCreateBo( pTop );
        pNet = Abc_NtkFindOrCreateNet( pTop, pOutputs[i] );
        Abc_ObjAddFanin( pBo, pBox );
        Abc_ObjAddFanin( pNet, pBo );
    }
    return pBox;
}

static Abc_Obj_t * If_CreateWhiteboxInstance( Abc_Ntk_t * pTop, Abc_Ntk_t * pModel, char * pInstName, char ** pInputs, char ** pOutputs )
{
    Abc_Obj_t * pBox, * pTerm, * pNet;
    int i;
    pBox = Abc_NtkCreateWhitebox( pTop );
    Abc_ObjAssignName( pBox, pInstName, NULL );
    Abc_ObjSetData( pBox, pModel );
    Abc_NtkForEachPi( pModel, pTerm, i )
    {
        Abc_Obj_t * pBi = Abc_NtkCreateBi( pTop );
        pNet = Abc_NtkFindOrCreateNet( pTop, pInputs[i] );
        Abc_ObjAddFanin( pBi, pNet );
        Abc_ObjAddFanin( pBox, pBi );
    }
    Abc_NtkForEachPo( pModel, pTerm, i )
    {
        Abc_Obj_t * pBo = Abc_NtkCreateBo( pTop );
        pNet = Abc_NtkFindOrCreateNet( pTop, pOutputs[i] );
        Abc_ObjAddFanin( pBo, pBox );
        Abc_ObjAddFanin( pNet, pBo );
    }
    return pBox;
}

static int If_ModuleIsSeq_rec( Abc_Ntk_t * pNtk, st__table * tMemo )
{
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pObj;
    char * pEntry;
    int i;
    if ( pNtk == NULL || tMemo == NULL )
        return 0;
    if ( st__lookup( tMemo, (char *)pNtk, &pEntry ) )
        return pEntry != NULL;
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        st__insert( tMemo, (char *)pNtk, (char *)1 );
        return 1;
    }
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        if ( Abc_ObjIsLatch(pObj) )
        {
            st__insert( tMemo, (char *)pNtk, (char *)1 );
            return 1;
        }
        if ( !Abc_ObjIsBlackbox(pObj) && !Abc_ObjIsWhitebox(pObj) )
            continue;
        pModel = (Abc_Ntk_t *)pObj->pData;
        if ( pModel && If_ModuleIsSeq_rec( pModel, tMemo ) )
        {
            st__insert( tMemo, (char *)pNtk, (char *)1 );
            return 1;
        }
    }
    st__insert( tMemo, (char *)pNtk, NULL );
    return 0;
}

static void If_DesignCountModuleKinds( Abc_Des_t * pDesign, Abc_Ntk_t * pTop, int * pnComb, int * pnSeq )
{
    st__table * tMemo;
    Abc_Ntk_t * pNtk;
    int i;
    *pnComb = 0;
    *pnSeq = 0;
    if ( pDesign == NULL )
        return;
    tMemo = st__init_table( st__ptrcmp, st__ptrhash );
    Vec_PtrForEachEntry( Abc_Ntk_t *, pDesign->vModules, pNtk, i )
    {
        if ( pNtk == pTop )
            continue;
        if ( If_ModuleIsSeq_rec( pNtk, tMemo ) )
            (*pnSeq)++;
        else
            (*pnComb)++;
    }
    st__free_table( tMemo );
}

static If_LibBox_t * If_DeriveBoxLibFromNtk( Abc_Ntk_t * pNtk, If_LibBox_t * pDelayLib, If_NewBoxLib_t * pNewBoxLib, FILE * pErr )
{
    Abc_Obj_t * pObj;
    If_LibBox_t * pLib;
    If_Box_t * pIfBox, * pDelayBox;
    If_NewBoxType_t * pNewType;
    int i;
    if ( pNtk == NULL )
        return NULL;
    pLib = If_LibBoxStart();
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        Abc_Ntk_t * pModel = NULL;
        char Buffer[1000];
        char * pName;
        int nPis, nPos, fBlack;
        int k;

        if ( pObj == NULL )
            continue;
        pModel = (pObj->Type == ABC_OBJ_WHITEBOX) ? Abc_ObjModel(pObj) : NULL;
        if ( pModel == NULL && pObj->Type == ABC_OBJ_BLACKBOX && Abc_ObjData(pObj) != NULL )
            pModel = (Abc_Ntk_t *)Abc_ObjData(pObj);
        pName  = pModel ? Abc_NtkName(pModel) : Abc_ObjName(pObj);
        nPis   = Abc_ObjFaninNum(pObj);
        nPos   = Abc_ObjFanoutNum(pObj);
        fBlack = (pObj->Type != ABC_OBJ_WHITEBOX);

        pIfBox = If_LibBoxFindBox( pLib, pName );
        if ( pIfBox != NULL )
        {
            if ( pIfBox->nPis != nPis || pIfBox->nPos != nPos || pIfBox->fBlack != fBlack )
            {
                sprintf( Buffer, "%s_%02d", pName, If_LibBoxNum(pLib) + 1 );
                pName = Buffer;
                pIfBox = NULL;
            }
            else
                continue;
        }
        if ( pIfBox == NULL )
        {
            pIfBox = If_BoxStart( Abc_UtilStrsav(pName), If_LibBoxNum(pLib) + 1, nPis, nPos, 0, fBlack, 0 );
            If_LibBoxAdd( pLib, pIfBox );
            pDelayBox = pDelayLib ? If_LibBoxFindBox( pDelayLib, pName ) : NULL;
            pNewType = pNewBoxLib ? If_NewBoxLibFindType( pNewBoxLib, pName ) : NULL;
            if ( pDelayBox && pDelayBox->nPis == nPis && pDelayBox->nPos == nPos && pDelayBox->fBlack == fBlack )
            {
                for ( k = 0; k < nPis * nPos; k++ )
                    pIfBox->pDelays[k] = pDelayBox->pDelays[k];
            }
            else if ( pNewType && pNewType->fHasTiming && pNewType->pDelays &&
                      pNewType->nInputs == nPis && pNewType->nOutputs == nPos )
            {
                for ( k = 0; k < nPis * nPos; k++ )
                    pIfBox->pDelays[k] = pNewType->pDelays[k];
            }
            else
            {
                for ( k = 0; k < nPis * nPos; k++ )
                    pIfBox->pDelays[k] = 1;
            }
        }
    }
    if ( If_LibBoxNum(pLib) == 0 )
    {
        fprintf( pErr, "Failed to derive any box entries from the boxed network.\n" );
        If_LibBoxFree( pLib );
        return NULL;
    }
    return pLib;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Package initialization procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_Init( Abc_Frame_t * pAbc )
{
    // set the default library
    If_LibLut_t s_LutLib = { "lutlib", 4, 0, {0,1,1,1,1}, {{0},{1},{1},{1},{1}} };
    Abc_FrameSetLibLut( If_LibLutDup(&s_LutLib) );

    Cmd_CommandAdd( pAbc, "FPGA mapping", "read_lut",   If_CommandReadLut,   0 ); 
    Cmd_CommandAdd( pAbc, "FPGA mapping", "print_lut",  If_CommandPrintLut,  0 ); 

    Cmd_CommandAdd( pAbc, "FPGA mapping", "read_cell",  If_CommandReadCell,  0 ); 
    Cmd_CommandAdd( pAbc, "FPGA mapping", "print_cell", If_CommandPrintCell, 0 ); 

    Cmd_CommandAdd( pAbc, "FPGA mapping", "read_box",   If_CommandReadBox,   0 ); 
    Cmd_CommandAdd( pAbc, "FPGA mapping", "print_box",  If_CommandPrintBox,  0 ); 
    Cmd_CommandAdd( pAbc, "FPGA mapping", "write_box",  If_CommandWriteBox,  0 ); 
    //Cmd_CommandAdd( pAbc, "FPGA mapping", "gen_box",    If_CommandGenBox,    0 ); 
    //Cmd_CommandAdd( pAbc, "FPGA mapping", "patch_box",  If_CommandPatchBox,  0 ); 
    Cmd_CommandAdd( pAbc, "FPGA mapping", "gen_design_boxes", If_CommandGenDesignBoxes, 0 ); 
    Cmd_CommandAdd( pAbc, "FPGA mapping", "print_tim",  If_CommandPrintTim,  0 ); 
}

/**Function*************************************************************

  Synopsis    [Package ending procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_End( Abc_Frame_t * pAbc )
{
    int i;
    for ( i = 0; i < ABC_LUT_LIBS; i++ )
        if ( Abc_FrameReadLibLutI(i) )
            If_LibLutFree( (If_LibLut_t *)Abc_FrameReadLibLutI(i) );
    If_LibBoxFree( (If_LibBox_t *)Abc_FrameReadLibBox() );
}

/**Function*************************************************************

  Synopsis    [Command procedure to read LUT libraries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandReadLut( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pFile;
    FILE * pOut, * pErr;
    If_LibLut_t * pLib;
    Abc_Ntk_t * pNet;
    char * FileName;
    int fVerbose;
    int c;

    pNet = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( argc == globalUtilOptind ) {
        fprintf( pErr, "The library file should be specified in the command line.\n" );
        goto usage;
    }
    if ( argc > globalUtilOptind + ABC_LUT_LIBS ) {
        fprintf( pErr, "Can read at most %d libraries. Quitting...\n", ABC_LUT_LIBS );
        goto usage;
    }

    // remove current libraries
    int i;
    for ( i = 0; i < ABC_LUT_LIBS; i++ )
        if ( Abc_FrameReadLibLutI(i) ) {
            If_LibLutFree( (If_LibLut_t *)Abc_FrameReadLibLutI(i) );
            Abc_FrameSetLibLutI( NULL, i );
        }

    // input new libraries
    for ( i = globalUtilOptind; i < argc; i++ ) {
        // get the input file name
        FileName = argv[i];
        if ( (pFile = fopen( FileName, "r" )) == NULL )
        {
            fprintf( pErr, "Cannot open input file \"%s\". ", FileName );
            if ( (FileName = Extra_FileGetSimilarName( FileName, ".genlib", ".lib", ".gen", ".g", NULL )) )
                fprintf( pErr, "Did you mean \"%s\"?", FileName );
            fprintf( pErr, "\n" );
            return 1;
        }
        fclose( pFile );
        // set the new network
        pLib = If_LibLutRead( FileName );
        if ( pLib == NULL )
        {
            fprintf( pErr, "Reading LUT library has failed.\n" );
            goto usage;
        }
        // replace the current library
        Abc_FrameSetLibLutI( pLib, i-globalUtilOptind );
    }
    return 0;

usage:
    fprintf( pErr, "\nusage: read_lut [-vh] <file1> <file2> ... <fileN>\n");
    fprintf( pErr, "\t          read the LUT library from the file(s)\n" );  
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    fprintf( pErr, "\t                                        \n");
    fprintf( pErr, "\t          File format for a LUT library:\n");
    fprintf( pErr, "\t          (the default library is shown)\n");
    fprintf( pErr, "\t                                        \n");
    fprintf( pErr, "\t          # The area/delay of k-variable LUTs:\n");
    fprintf( pErr, "\t          # k  area   delay\n");
    fprintf( pErr, "\t          1      1      1\n");
    fprintf( pErr, "\t          2      2      2\n");
    fprintf( pErr, "\t          3      4      3\n");
    fprintf( pErr, "\t          4      8      4\n");
    fprintf( pErr, "\t          5     16      5\n");
    fprintf( pErr, "\t          6     32      6\n");
    return 1;       /* error exit */
}

/**Function*************************************************************

  Synopsis    [Command procedure to read LUT libraries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandPrintLut( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNet;
    int fVerbose;
    int c;

    pNet = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( argc != globalUtilOptind )
        goto usage;

    // set the new network
    int i;
    for ( i = 0; i < ABC_LUT_LIBS; i++ )
        if ( Abc_FrameReadLibLutI(i) )
            If_LibLutPrint( (If_LibLut_t *)Abc_FrameReadLibLutI(i) );
    return 0;

usage:
    fprintf( pErr, "\nusage: print_lut [-vh]\n");
    fprintf( pErr, "\t          print the current LUT library\n" );  
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    return 1;       /* error exit */
}

/**Function*************************************************************

  Synopsis    [Command procedure to read LUT libraries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandReadCell( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pFile;
    FILE * pOut, * pErr;
    If_LibCell_t * pLib;
    Abc_Ntk_t * pNet;
    char * FileName;
    int fVerbose;
    int c;

    pNet = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( argc == globalUtilOptind ) {
        fprintf( pErr, "The library file should be specified in the command line.\n" );
        goto usage;
    }

    // remove current libraries
    If_LibCellFree( (If_LibCell_t *)Abc_FrameReadLibCell() );
    Abc_FrameSetLibCell( NULL );

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pErr, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".genlib", ".lib", ".gen", ".g", NULL )) )
            fprintf( pErr, "Did you mean \"%s\"?", FileName );
        fprintf( pErr, "\n" );
        return 1;
    }
    fclose( pFile );
    // set the new network
    pLib = If_LibCellRead( FileName );
    if ( pLib == NULL )
    {
        fprintf( pErr, "Reading LUT library has failed.\n" );
        goto usage;
    }
    // replace the current library
    Abc_FrameSetLibCell( pLib );
    return 0;

usage:
    fprintf( pErr, "\nusage: read_cell [-vh] <file>\n");
    fprintf( pErr, "\t          read the cell library from the file\n" );  
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    return 1;       /* error exit */
}

/**Function*************************************************************

  Synopsis    [Command procedure to read cell libraries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandPrintCell( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNet;
    int fVerbose;
    int c;

    pNet = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( argc != globalUtilOptind )
        goto usage;

    // set the new network
    If_LibCellPrint( (If_LibCell_t *)Abc_FrameReadLibCell() );
    return 0;

usage:
    fprintf( pErr, "\nusage: print_cell [-vh]\n");
    fprintf( pErr, "\t          print the current cell library\n" );  
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    return 1;       /* error exit */
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandReadBox( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pFile;
    FILE * pOut, * pErr;
    If_LibBox_t * pLib;
    Abc_Ntk_t * pNet;
    char * FileName;
    int fExtended;
    int fVerbose;
    int c;

    pNet = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fExtended = 0;
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "evh")) != EOF ) 
    {
        switch (c) 
        {
            case 'e':
                fExtended ^= 1;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( argc != globalUtilOptind + 1 )
        goto usage;

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        fprintf( pErr, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".genlib", ".lib", ".gen", ".g", NULL )) )
            fprintf( pErr, "Did you mean \"%s\"?", FileName );
        fprintf( pErr, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pLib = fExtended ? If_LibBoxRead2( FileName ) : If_LibBoxRead( FileName );
    if ( pLib == NULL )
    {
        fprintf( pErr, "Reading box library has failed.\n" );
        goto usage;
    }
    // replace the current library
    If_LibBoxFree( (If_LibBox_t *)Abc_FrameReadLibBox() );
    Abc_FrameSetLibBox( pLib );
    return 0;

usage:
    fprintf( pErr, "\nusage: read_box [-evh]\n");
    fprintf( pErr, "\t          read the box library from the file\n" );  
    fprintf( pErr, "\t-e      : toggles reading extended format [default = %s]\n", (fExtended? "yes" : "no") );
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    return 1;       /* error exit */
}

/**Function*************************************************************

  Synopsis    [Command procedure to read LUT libraries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandPrintBox( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNet;
    int fVerbose;
    int c;

    pNet = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    // set the defaults
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( argc != globalUtilOptind )
        goto usage;

    // set the new network
    If_LibBoxPrint( stdout, (If_LibBox_t *)Abc_FrameReadLibBox() );
    return 0;

usage:
    fprintf( pErr, "\nusage: print_box [-vh]\n");
    fprintf( pErr, "\t          print the current box library\n" );  
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    return 1;       /* error exit */
}

/**Function*************************************************************

  Synopsis    [Command procedure to read LUT libraries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandWriteBox( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNet;
    int fVerbose;
    int c;

    pNet = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( argc != globalUtilOptind+1 )
        goto usage;

    If_LibBoxWrite( argv[globalUtilOptind], (If_LibBox_t *)Abc_FrameReadLibBox() );
    return 0;

usage:
    fprintf( pErr, "\nusage: write_box [-vh] <file>\n");
    fprintf( pErr, "\t          write the current box library into a file\n" );  
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    fprintf( pErr, "\t<file>  : the output file name\n");
    return 1;       /* error exit */
}

/**Function*************************************************************

  Synopsis    [Command procedure to generate one box-library entry.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*int If_CommandGenBox( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj;
    If_LibBox_t * pLib, * pDelayLib;
    If_Box_t * pIfBox, * pDelayBox;
    char * pFileName;
    char * pDelayFile;
    int fVerbose, DelayScale;
    int c, i;

    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);
    pNtk = Abc_FrameReadNtk(pAbc);

    fVerbose = 1;
    DelayScale = 100;
    pDelayFile = NULL;
    pDelayLib = NULL;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "d:s:vh")) != EOF )
    {
        switch (c)
        {
            case 'd':
                pDelayFile = (char *)globalUtilOptarg;
                break;
            case 's':
                DelayScale = atoi( globalUtilOptarg );
                if ( DelayScale <= 0 )
                {
                    fprintf( pErr, "Delay scale should be a positive integer.\n" );
                    return 1;
                }
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( pDelayFile )
    {
        pDelayLib = If_LibBoxRead( pDelayFile );
        if ( pDelayLib == NULL )
        {
            fprintf( pErr, "Cannot read delay source file \"%s\".\n", pDelayFile );
            return 1;
        }
    }

    pFileName = argv[globalUtilOptind];
    if ( argc == globalUtilOptind + 1 )
    {
        pLib = (If_LibBox_t *)Abc_FrameReadLibBox();
        if ( pLib != NULL )
        {
            if ( pDelayLib )
            {
                fprintf( pErr, "Option -d is only used when deriving boxes from the current network.\n" );
                If_LibBoxFree( pDelayLib );
                return 1;
            }
            If_LibBoxWrite( pFileName, pLib );
            if ( fVerbose )
                fprintf( pOut, "Dumped the current box library into \"%s\".\n", pFileName );
            return 0;
        }

        if ( pNtk == NULL )
        {
            if ( pDelayLib )
                If_LibBoxFree( pDelayLib );
            fprintf( pErr, "There is no current network.\n" );
            return 1;
        }
        if ( Abc_NtkBoxNum(pNtk) == 0 )
        {
            if ( pDelayLib )
                If_LibBoxFree( pDelayLib );
            fprintf( pErr, "The current network does not contain boxes and there is no current box library.\n" );
            return 1;
        }

        pLib = If_LibBoxStart();
        Abc_NtkForEachBox( pNtk, pObj, i )
        {
            Abc_Ntk_t * pModel = NULL;
            char Buffer[1000];
            char * pName;
            int nPis, nPos, fBlack;
            int k;

            if ( pObj == NULL )
                continue;
            pModel  = (pObj->Type == ABC_OBJ_WHITEBOX) ? Abc_ObjModel(pObj) : NULL;
            if ( pModel == NULL && pObj->Type == ABC_OBJ_BLACKBOX && Abc_ObjData(pObj) != NULL )
                pModel = (Abc_Ntk_t *)Abc_ObjData(pObj);
            pName   = pModel ? Abc_NtkName(pModel) : Abc_ObjName(pObj);
            nPis    = Abc_ObjFaninNum(pObj);
            nPos    = Abc_ObjFanoutNum(pObj);
            fBlack  = (pObj->Type != ABC_OBJ_WHITEBOX);

            pIfBox = If_LibBoxFindBox( pLib, pName );
            if ( pIfBox != NULL )
            {
                if ( pIfBox->nPis != nPis || pIfBox->nPos != nPos || pIfBox->fBlack != fBlack )
                {
                    sprintf( Buffer, "%s_%02d", pName, If_LibBoxNum(pLib) + 1 );
                    pName = Buffer;
                    pIfBox = NULL;
                }
                else
                    continue;
            }

            if ( pIfBox == NULL )
            {
                pIfBox = If_BoxStart( Abc_UtilStrsav(pName), If_LibBoxNum(pLib) + 1, nPis, nPos, 0, fBlack, 0 );
                If_LibBoxAdd( pLib, pIfBox );
                pDelayBox = pDelayLib ? If_LibBoxFindBox( pDelayLib, pName ) : NULL;
                if ( pDelayBox && pDelayBox->nPis == nPis && pDelayBox->nPos == nPos && pDelayBox->fBlack == fBlack )
                    for ( k = 0; k < nPis * nPos; k++ )
                        pIfBox->pDelays[k] = pDelayBox->pDelays[k];
                else
                    for ( k = 0; k < nPis * nPos; k++ )
                        pIfBox->pDelays[k] = 1;
            }
        }

        if ( If_LibBoxNum(pLib) == 0 )
        {
            If_LibBoxFree( pLib );
            if ( pDelayLib )
                If_LibBoxFree( pDelayLib );
            fprintf( pErr, "Failed to derive any box entries from the current network.\n" );
            return 1;
        }

        If_LibBoxWrite( pFileName, pLib );
        if ( fVerbose )
            fprintf( pOut, "Generated box library \"%s\" from the current network%s.\n", pFileName, pDelayLib ? " using delays from the delay source file when available":" using unit delays" );
        If_LibBoxFree( pLib );
        if ( pDelayLib )
            If_LibBoxFree( pDelayLib );
        return 0;
    }

    if ( argc < globalUtilOptind + 7 )
        goto usage;
    if ( pDelayLib )
    {
        fprintf( pErr, "Option -d is not supported together with explicit box specifications.\n" );
        If_LibBoxFree( pDelayLib );
        return 1;
    }

    pLib = If_LibBoxStart();
    i = globalUtilOptind + 1;
    while ( i < argc )
    {
        char * pName, * pDelay;
        int Id, Type, nPis, nPos, nDelays, Delay, k;

        if ( i + 5 >= argc )
        {
            fprintf( pErr, "Incomplete box specification near argument %d.\n", i - globalUtilOptind );
            If_LibBoxFree( pLib );
            return 1;
        }

        pName   = argv[i + 0];
        Id      = atoi( argv[i + 1] );
        Type    = atoi( argv[i + 2] );
        nPis    = atoi( argv[i + 3] );
        nPos    = atoi( argv[i + 4] );
        nDelays = nPis * nPos;

        if ( Type != 0 && Type != 1 )
        {
            fprintf( pErr, "The box type should be 0 (black) or 1 (white) for box \"%s\".\n", pName );
            If_LibBoxFree( pLib );
            return 1;
        }
        if ( Id < 0 )
        {
            fprintf( pErr, "The box ID should be non-negative for box \"%s\".\n", pName );
            If_LibBoxFree( pLib );
            return 1;
        }
        if ( nPis <= 0 || nPos <= 0 )
        {
            fprintf( pErr, "The number of inputs/outputs should be positive for box \"%s\".\n", pName );
            If_LibBoxFree( pLib );
            return 1;
        }
        if ( i + 5 + nDelays > argc )
        {
            fprintf( pErr, "The box \"%s\" needs %d delay values.\n", pName, nDelays );
            If_LibBoxFree( pLib );
            return 1;
        }
        if ( Id < Vec_PtrSize(pLib->vBoxes) && Vec_PtrEntry(pLib->vBoxes, Id) != NULL )
        {
            fprintf( pErr, "The box ID %d is used more than once.\n", Id );
            If_LibBoxFree( pLib );
            return 1;
        }

        pIfBox = If_BoxStart( Abc_UtilStrsav(pName), Id, nPis, nPos, 0, !Type, 0 );
        If_LibBoxAdd( pLib, pIfBox );
        for ( k = 0; k < nDelays; k++ )
        {
            pDelay = argv[i + 5 + k];
            if ( !If_ParseDelayValue( pDelay, DelayScale, &Delay ) )
            {
                fprintf( pErr, "Cannot parse delay value \"%s\" for box \"%s\".\n", pDelay, pName );
                If_LibBoxFree( pLib );
                return 1;
            }
            pIfBox->pDelays[k] = Delay;
        }
        i += 5 + nDelays;
    }

    If_LibBoxWrite( pFileName, pLib );
    if ( fVerbose )
        fprintf( pOut, "Generated box library \"%s\" with %d explicit box entries.\n", pFileName, If_LibBoxNum(pLib) );
    If_LibBoxFree( pLib );
    return 0;

usage:
    if ( pDelayLib )
        If_LibBoxFree( pDelayLib );
    fprintf( pErr, "\nusage: gen_box [-d delay.box] [-s scale] [-vh] <file>\n");
    fprintf( pErr, "\t          write the current box library into a file if it exists\n" );
    fprintf( pErr, "\t          otherwise derive one from boxes in the current network\n" );
    fprintf( pErr, "\t          using delay.box when a matching box exists, otherwise unit delays\n" );
    fprintf( pErr, "\t       or gen_box [-s scale] [-vh] <file> <name1> <id1> <type1> <nInputs1> <nOutputs1> <delay...>\n" );
    fprintf( pErr, "\t                          [<name2> <id2> <type2> <nInputs2> <nOutputs2> <delay...>] ...\n" );
    fprintf( pErr, "\t-d     : box-library file used as the delay source for inferred boxes\n" );
    fprintf( pErr, "\t-s     : multiply decimal delays by this positive integer before storing [default = %d]\n", DelayScale );
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    fprintf( pErr, "\t<file>  : the output box-library file name\n");
    fprintf( pErr, "\t<type>  : 1 for white box, 0 for black box\n");
    fprintf( pErr, "\t<delay> : integer delay or '-' for no connection\n");
    return 1;
}*/

/**Function*************************************************************

  Synopsis    [Command procedure to patch delay values of one box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*int If_CommandPatchBox( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    If_LibBox_t * pLib = NULL;
    If_Box_t * pBox;
    char * pFileName = NULL, * pBoxName, * pDelay;
    int fVerbose, fCurrent, DelayScale;
    int c, i, Delay, nDelays, iStart;

    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    fVerbose = 1;
    fCurrent = 0;
    DelayScale = 100;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "cs:vh")) != EOF )
    {
        switch (c)
        {
            case 'c':
                fCurrent ^= 1;
                break;
            case 's':
                DelayScale = atoi( globalUtilOptarg );
                if ( DelayScale <= 0 )
                {
                    fprintf( pErr, "Delay scale should be a positive integer.\n" );
                    return 1;
                }
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( fCurrent )
    {
        if ( argc < globalUtilOptind + 2 )
            goto usage;
        pLib = (If_LibBox_t *)Abc_FrameReadLibBox();
        if ( pLib == NULL )
        {
            fprintf( pErr, "There is no current box library loaded.\n" );
            return 1;
        }
        pBoxName = argv[globalUtilOptind];
        iStart = globalUtilOptind + 1;
    }
    else
    {
        if ( argc < globalUtilOptind + 3 )
            goto usage;
        pFileName = argv[globalUtilOptind];
        pLib = If_LibBoxRead( pFileName );
        if ( pLib == NULL )
        {
            fprintf( pErr, "Reading box library file \"%s\" has failed.\n", pFileName );
            return 1;
        }
        pBoxName = argv[globalUtilOptind + 1];
        iStart = globalUtilOptind + 2;
    }

    pBox = If_LibBoxFindBox( pLib, pBoxName );
    if ( pBox == NULL )
    {
        fprintf( pErr, "Cannot find box \"%s\".\n", pBoxName );
        if ( !fCurrent )
            If_LibBoxFree( pLib );
        return 1;
    }

    nDelays = pBox->nPis * pBox->nPos;
    if ( argc != iStart + nDelays )
    {
        fprintf( pErr, "Box \"%s\" expects %d delay values.\n", pBoxName, nDelays );
        if ( !fCurrent )
            If_LibBoxFree( pLib );
        return 1;
    }

    for ( i = 0; i < nDelays; i++ )
    {
        pDelay = argv[iStart + i];
        if ( !If_ParseDelayValue( pDelay, DelayScale, &Delay ) )
        {
            fprintf( pErr, "Cannot parse delay value \"%s\".\n", pDelay );
            if ( !fCurrent )
                If_LibBoxFree( pLib );
            return 1;
        }
        pBox->pDelays[i] = Delay;
    }

    if ( fCurrent )
    {
        if ( fVerbose )
            fprintf( pOut, "Patched delays of box \"%s\" in the current box library.\n", pBoxName );
        return 0;
    }

    If_LibBoxWrite( pFileName, pLib );
    if ( fVerbose )
        fprintf( pOut, "Patched delays of box \"%s\" in file \"%s\".\n", pBoxName, pFileName );
    If_LibBoxFree( pLib );
    return 0;

usage:
    fprintf( pErr, "\nusage: patch_box [-c] [-s scale] [-vh] <file> <name> <delay1> ... <delayN>\n");
    fprintf( pErr, "\t          patch delay values of one box in a box-library file\n" );
    fprintf( pErr, "\t       or patch_box -c [-s scale] [-vh] <name> <delay1> ... <delayN>\n");
    fprintf( pErr, "\t          patch delay values of one box in the current box library\n" );
    fprintf( pErr, "\t-c      : patch the current in-memory box library instead of a file [default = %s]\n", (fCurrent? "yes" : "no") );
    fprintf( pErr, "\t-s      : multiply decimal delays by this positive integer before storing [default = %d]\n", DelayScale );
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    fprintf( pErr, "\t<delay> : integer delay or '-' for no connection\n");
    return 1;
}*/

/**Function*************************************************************

  Synopsis    [Exports the current network as hierarchical BLIF with preserved boxes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandGenDesignBoxes( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pTopDup = NULL;
    Abc_Des_t * pDesign = NULL;
    If_NewBoxLib_t * pNewBoxLib = NULL;
    If_LibBox_t * pBoxLib = NULL, * pDelayLib = NULL;
    char * pFileName, * pBoxFileName = NULL, * pDelayFile = NULL;
    int c, fVerbose = 1, fStatus = 1, nComb = 0, nSeq = 0;

    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);
    pNtk = Abc_FrameReadNtk(pAbc);

    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "d:vh")) != EOF )
    {
        switch (c)
        {
            case 'd':
                pDelayFile = (char *)globalUtilOptarg;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 && argc != globalUtilOptind + 2 )
        goto usage;
    if ( pNtk == NULL )
    {
        fprintf( pErr, "There is no current network.\n" );
        return 1;
    }
    if ( pDelayFile )
    {
        pDelayLib = If_LibBoxRead( pDelayFile );
        if ( pDelayLib == NULL )
        {
            fprintf( pErr, "Cannot read delay source file \"%s\".\n", pDelayFile );
            return 1;
        }
    }

    pFileName = argv[globalUtilOptind];
    if ( argc == globalUtilOptind + 2 )
        pBoxFileName = argv[globalUtilOptind + 1];
    if ( pNtk->pDesign == NULL || pNtk->pDesign->vModules == NULL || Vec_PtrSize(pNtk->pDesign->vModules) <= 1 )
    {
        fprintf( pErr, "The current network does not belong to a preserved hierarchical design.\n" );
        fprintf( pErr, "Read the design with hierarchy preserved before calling gen_design_boxes.\n" );
        return 1;
    }
    pDesign = Abc_DesDup( pNtk->pDesign );
    pTopDup = pNtk->pCopy;
    if ( pDesign == NULL || pTopDup == NULL )
    {
        fprintf( pErr, "Failed to duplicate the current hierarchical design.\n" );
        goto cleanup;
    }
    pNewBoxLib = If_NewBoxLibAttachHierarchy( pTopDup );
    if ( pNewBoxLib == NULL )
    {
        fprintf( pErr, "Failed to attach box metadata to the duplicated top-level network.\n" );
        goto cleanup;
    }
    If_DesignCountModuleKinds( pDesign, pTopDup, &nComb, &nSeq );
    Io_WriteBlif( pTopDup, pFileName, 1, 0, 0 );
    if ( pBoxFileName )
    {
        pBoxLib = If_DeriveBoxLibFromNtk( pTopDup, pDelayLib, pNewBoxLib, pErr );
        if ( pBoxLib == NULL )
            goto cleanup;
        If_LibBoxWrite( pBoxFileName, pBoxLib );
    }
    fStatus = 0;
    if ( fVerbose )
    {
        fprintf( pOut, "Exported hierarchical design rooted at \"%s\" into \"%s\" with %d boxed module type(s): %d combinational and %d sequential.\n",
            Abc_NtkName(pTopDup), pFileName, Vec_PtrSize(pDesign->vModules) - 1, nComb, nSeq );
        if ( pBoxFileName )
        {
            if ( pDelayLib )
                fprintf( pOut, "Wrote companion box library into \"%s\" for read_box/build_tim using delay source data from \"%s\" when names match.\n",
                    pBoxFileName, pDelayFile );
            else
                fprintf( pOut, "Wrote companion box library into \"%s\" for read_box/build_tim.\n", pBoxFileName );
        }
    }

cleanup:
    if ( pDelayLib )
        If_LibBoxFree( pDelayLib );
    if ( pBoxLib )
        If_LibBoxFree( pBoxLib );
    if ( pDesign )
        Abc_DesFree( pDesign, NULL );
    return fStatus;

usage:
    fprintf( pErr, "\nusage: gen_design_boxes [-d delay.box] [-vh] <file.blif> [file.box]\n");
    fprintf( pErr, "\t          export the current hierarchical design with all non-top module types emitted as boxes\n" );
    fprintf( pErr, "\t          module kinds are inferred automatically as combinational or sequential\n" );
    fprintf( pErr, "\t[file.box]: optional companion box library for read_box/build_tim\n" );
    fprintf( pErr, "\t-d      : optional delay source box-library file; matching entries override unit delays\n" );
    fprintf( pErr, "\t          if no matching delay source exists, ifNewBox timing metadata is used when available\n" );
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds timing manager in the &-space from preserved black boxes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*int If_CommandBuildTim( Abc_Frame_t * pAbc, int argc, char **argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkNoBox = NULL, * pNtkLogic = NULL, * pNtkStrash = NULL;
    Gia_Man_t * pGia = NULL;
    If_LibBox_t * pLibBox;
    Tim_Man_t * pTim;
    Abc_Obj_t * pBox, * pTerm, * pPoNew, * pPiNew;
    Abc_Obj_t * pNet, * pNetNew;
    If_Box_t * pIfBox;
    char * pName;
    int c, fVerbose = 0, fStatus = 1, i, k;

    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);
    pNtk = Abc_FrameReadNtk(pAbc);
    pLibBox = (If_LibBox_t *)Abc_FrameReadLibBox();

    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( pNtk == NULL )
    {
        fprintf( pErr, "There is no current network.\n" );
        return 1;
    }
    if ( pLibBox == NULL )
    {
        fprintf( pErr, "There is no current box library loaded.\n" );
        return 1;
    }
    if ( !Abc_NtkIsNetlist(pNtk) )
    {
        fprintf( pErr, "The current network should be a netlist with preserved boxes.\n" );
        return 1;
    }
    if ( Abc_NtkWhiteboxNum(pNtk) > 0 )
    {
        fprintf( pErr, "build_tim currently supports black boxes only. The network has %d white box(es).\n", Abc_NtkWhiteboxNum(pNtk) );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        fprintf( pErr, "build_tim currently does not support latch objects. Use preserved DFF subckts as black boxes instead.\n" );
        return 1;
    }
    if ( Abc_NtkBlackboxNum(pNtk) == 0 )
    {
        fprintf( pErr, "The current network does not contain black boxes.\n" );
        return 1;
    }

    pNtkNoBox = Abc_NtkConvertBlackboxes( pNtk );
    if ( pNtkNoBox == NULL )
        return 1;
    if ( Abc_NtkLatchNum(pNtkNoBox) > 0 )
    {
        fprintf( pErr, "The converted network unexpectedly contains latch objects.\n" );
        goto cleanup;
    }

    pTim = Tim_ManStart( Abc_NtkPiNum(pNtkNoBox), Abc_NtkPoNum(pNtkNoBox) );
    Abc_NtkForEachBlackbox( pNtk, pBox, i )
    {
        int nIns = Abc_ObjFaninNum(pBox);
        int nOuts = Abc_ObjFanoutNum(pBox);
        int firstIn = -1, firstOut = -1;
        pName = If_BoxInstanceName( pBox );
        pIfBox = If_LibBoxFindBox( pLibBox, pName );
        if ( pIfBox == NULL )
        {
            fprintf( pErr, "Cannot find box \"%s\" in the current box library.\n", pName );
            goto cleanup;
        }
        if ( pIfBox->nPis != nIns || pIfBox->nPos != nOuts )
        {
            fprintf( pErr, "Box \"%s\" has shape %d x %d in the network but %d x %d in the current box library.\n",
                pName, nIns, nOuts, pIfBox->nPis, pIfBox->nPos );
            goto cleanup;
        }

        Abc_ObjForEachFanin( pBox, pTerm, k )
        {
            int Index;
            pNet = Abc_ObjFanin0( pTerm );
            pNetNew = pNet ? pNet->pCopy : NULL;
            pPoNew = If_FindNetPo( pNetNew );
            if ( pPoNew == NULL )
            {
                fprintf( pErr, "Cannot locate the extracted PO for input %d of box \"%s\".\n", k, pName );
                goto cleanup;
            }
            Index = If_FindPoIndex( pNtkNoBox, pPoNew );
            if ( Index < 0 )
            {
                fprintf( pErr, "Cannot locate the PO index for input %d of box \"%s\".\n", k, pName );
                goto cleanup;
            }
            if ( k == 0 )
                firstIn = Index;
            else if ( Index != firstIn + k )
            {
                fprintf( pErr, "Box \"%s\" does not have contiguous extracted input POs.\n", pName );
                goto cleanup;
            }
        }
        Abc_ObjForEachFanout( pBox, pTerm, k )
        {
            int Index;
            pPiNew = pTerm->pCopy;
            if ( pPiNew == NULL )
            {
                fprintf( pErr, "Cannot locate the extracted PI for output %d of box \"%s\".\n", k, pName );
                goto cleanup;
            }
            Index = If_FindPiIndex( pNtkNoBox, pPiNew );
            if ( Index < 0 )
            {
                fprintf( pErr, "Cannot locate the PI index for output %d of box \"%s\".\n", k, pName );
                goto cleanup;
            }
            if ( k == 0 )
                firstOut = Index;
            else if ( Index != firstOut + k )
            {
                fprintf( pErr, "Box \"%s\" does not have contiguous extracted output PIs.\n", pName );
                goto cleanup;
            }
        }
        Tim_ManCreateBox( pTim, firstIn, nIns, firstOut, nOuts, pIfBox->Id, pIfBox->fBlack );
        if ( fVerbose )
            fprintf( pOut, "Mapped box \"%s\": POs [%d..%d], PIs [%d..%d], table %d.\n",
                pName, firstIn, firstIn + nIns - 1, firstOut, firstOut + nOuts - 1, pIfBox->Id );
    }
    Tim_ManCreate( pTim, pLibBox, NULL, NULL );

    pNtkLogic = Abc_NtkToLogic( pNtkNoBox );
    if ( pNtkLogic == NULL )
    {
        fprintf( pErr, "Converting the extracted network to logic has failed.\n" );
        goto cleanup;
    }
    pNtkStrash = Abc_NtkStrash( pNtkLogic, 0, 1, 0 );
    if ( pNtkStrash == NULL )
    {
        fprintf( pErr, "Strashing the extracted network has failed.\n" );
        goto cleanup;
    }
    pGia = Abc_NtkAigToGia( pNtkStrash, 0 );
    if ( pGia == NULL )
    {
        fprintf( pErr, "Converting the extracted AIG to GIA has failed.\n" );
        goto cleanup;
    }
    if ( Gia_ManCiNum(pGia) != Abc_NtkPiNum(pNtkNoBox) || Gia_ManCoNum(pGia) != Abc_NtkPoNum(pNtkNoBox) )
    {
        fprintf( pErr, "The extracted GIA has %d CIs / %d COs, but the timing manager expects %d PIs / %d POs.\n",
            Gia_ManCiNum(pGia), Gia_ManCoNum(pGia), Abc_NtkPiNum(pNtkNoBox), Abc_NtkPoNum(pNtkNoBox) );
        goto cleanup;
    }
    pGia->pManTime = pTim;
    pTim = NULL;
    Abc_FrameUpdateGia( pAbc, pGia );
    pGia = NULL;
    fStatus = 0;
    if ( fVerbose )
        fprintf( pOut, "Built timing manager with %d box(es), %d CIs, and %d COs.\n",
            Tim_ManBoxNum((Tim_Man_t *)Abc_FrameReadGia(pAbc)->pManTime),
            Gia_ManCiNum(Abc_FrameReadGia(pAbc)),
            Gia_ManCoNum(Abc_FrameReadGia(pAbc)) );

cleanup:
    if ( pGia )
        Gia_ManStop( pGia );
    if ( pNtkStrash )
        Abc_NtkDelete( pNtkStrash );
    if ( pNtkLogic )
        Abc_NtkDelete( pNtkLogic );
    if ( pNtkNoBox )
        Abc_NtkDelete( pNtkNoBox );
    if ( pTim )
        Tim_ManStop( pTim );
    return fStatus;

usage:
    fprintf( pErr, "\nusage: build_tim [-vh]\n");
    fprintf( pErr, "\t          build the timing manager in the &-space from preserved black boxes\n" );
    fprintf( pErr, "\t          requires read_blif -p and a current box library loaded by read_box\n" );
    fprintf( pErr, "\t          currently supports combinational black-box netlists only\n" );
    fprintf( pErr, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    fprintf( pErr, "\t-h      : print the command usage\n");
    return 1;
}*/


/**Function*************************************************************

  Synopsis    [Command procedure to read LUT libraries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CommandPrintTim( Abc_Frame_t * pAbc, int argc, char **argv )
{
    Gia_Man_t * pGia = Abc_FrameReadGia(pAbc);
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF ) 
    {
        switch (c) 
        {
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }
    if ( pGia == NULL )
    {
        Abc_Print( -1, "There is no AIG in the &-space.\n" );
        return 1;
    }
    if ( pGia->pManTime == NULL )
    {
        Abc_Print( -1, "The current AIG does not have a timing manager.\n" );
        return 1;
    }
    Tim_ManPrint( (Tim_Man_t *)pGia->pManTime );
    if ( fVerbose ) 
        Tim_ManPrintBoxCopy( (Tim_Man_t *)pGia->pManTime );
    return 0;

usage:
    Abc_Print( -2, "\nusage: print_tim [-vh]\n");
    Abc_Print( -2, "\t          print the timing manager\n" );  
    Abc_Print( -2, "\t-v      : toggles enabling of verbose output [default = %s]\n", (fVerbose? "yes" : "no") );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;       /* error exit */
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
