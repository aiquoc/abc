#include "base/abc/abc.h"
#include "ifNewBox.h"

ABC_NAMESPACE_IMPL_START

static Vec_Att_t * If_NewBoxAttrMan( Abc_Ntk_t * pNtk )
{
    return pNtk ? (Vec_Att_t *)Vec_PtrEntry( pNtk->vAttrs, VEC_ATTR_DATA1 ) : NULL;
}

static char * If_NewBoxStrsav( char * pName )
{
    return pName ? Abc_UtilStrsav( pName ) : NULL;
}

static char * If_NewBoxDeriveTypeName( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pModel = NULL;
    if ( Abc_ObjIsWhitebox(pObj) )
        pModel = Abc_ObjModel(pObj);
    else if ( Abc_ObjIsBlackbox(pObj) && Abc_ObjData(pObj) != NULL )
        pModel = (Abc_Ntk_t *)Abc_ObjData(pObj);
    if ( pModel )
        return Abc_NtkName( pModel );
    if ( Abc_ObjIsLatch(pObj) )
        return "ABC_LATCH";
    return Abc_ObjName( pObj );
}

static If_NewBoxClass_t If_NewBoxDeriveClass( Abc_Obj_t * pObj )
{
    Abc_Ntk_t * pModel = NULL;
    if ( Abc_ObjIsLatch(pObj) )
        return IF_NEWBOX_FLOP;
    if ( Abc_ObjIsWhitebox(pObj) )
        pModel = Abc_ObjModel(pObj);
    else if ( Abc_ObjIsBlackbox(pObj) && Abc_ObjData(pObj) != NULL )
        pModel = (Abc_Ntk_t *)Abc_ObjData(pObj);
    if ( pModel == NULL || Abc_NtkHasBlackbox(pModel) || !Abc_NtkPiNum(pModel) || !Abc_NtkPoNum(pModel) )
        return IF_NEWBOX_BOX;
    return Abc_NtkLatchNum(pModel) > 0 ? IF_NEWBOX_FLOP : IF_NEWBOX_BYPASS;
}

static If_NewBoxKind_t If_NewBoxDeriveKind( Abc_Obj_t * pObj )
{
    return Abc_ObjIsLatch(pObj) ? IF_NEWBOX_SEQ : IF_NEWBOX_COMB;
}

static If_NewBoxColor_t If_NewBoxDeriveColor( Abc_Obj_t * pObj )
{
    return If_NewBoxDeriveClass(pObj) == IF_NEWBOX_BOX ? IF_NEWBOX_BLACK : IF_NEWBOX_WHITE;
}

static If_NewBoxKeep_t If_NewBoxDeriveKeep( Abc_Obj_t * pObj )
{
    return IF_NEWBOX_MUST_KEEP;
}

static int If_NewBoxPortCount( int nInputs, int nOutputs )
{
    return nInputs + nOutputs;
}

static void If_NewBoxDerivePortsFromModel( If_NewBoxType_t * pType, Abc_Ntk_t * pModel )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachPi( pModel, pObj, i )
        If_NewBoxTypeSetPort( pType, i, Abc_ObjName(Abc_ObjFanout0(pObj)), IF_NEWBOX_PORT_IN, 1 );
    Abc_NtkForEachPo( pModel, pObj, i )
        If_NewBoxTypeSetPort( pType, pType->nInputs + i, Abc_ObjName(Abc_ObjFanin0(pObj)), IF_NEWBOX_PORT_OUT, 1 );
}

static void If_NewBoxDeriveDefaultPorts( If_NewBoxType_t * pType )
{
    char Buffer[64];
    int i;
    if ( pType->Kind == IF_NEWBOX_SEQ && pType->nInputs == 1 && pType->nOutputs == 1 )
    {
        If_NewBoxTypeSetPort( pType, 0, "D", IF_NEWBOX_PORT_IN, 1 );
        If_NewBoxTypeSetPort( pType, 1, "Q", IF_NEWBOX_PORT_OUT, 1 );
        return;
    }
    for ( i = 0; i < pType->nInputs; i++ )
    {
        sprintf( Buffer, "in%d", i );
        If_NewBoxTypeSetPort( pType, i, Buffer, IF_NEWBOX_PORT_IN, 1 );
    }
    for ( i = 0; i < pType->nOutputs; i++ )
    {
        sprintf( Buffer, "out%d", i );
        If_NewBoxTypeSetPort( pType, pType->nInputs + i, Buffer, IF_NEWBOX_PORT_OUT, 1 );
    }
}

static int If_NewBoxModelIsSeq_rec( Abc_Ntk_t * pNtk, st__table * tMemo )
{
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
        Abc_Ntk_t * pModel = NULL;
        if ( Abc_ObjIsLatch(pObj) )
        {
            st__insert( tMemo, (char *)pNtk, (char *)1 );
            return 1;
        }
        if ( !Abc_ObjIsBlackbox(pObj) && !Abc_ObjIsWhitebox(pObj) )
            continue;
        if ( Abc_ObjIsWhitebox(pObj) )
            pModel = Abc_ObjModel(pObj);
        else if ( Abc_ObjData(pObj) != NULL )
            pModel = (Abc_Ntk_t *)Abc_ObjData(pObj);
        if ( pModel && If_NewBoxModelIsSeq_rec( pModel, tMemo ) )
        {
            st__insert( tMemo, (char *)pNtk, (char *)1 );
            return 1;
        }
    }
    st__insert( tMemo, (char *)pNtk, NULL );
    return 0;
}

If_NewBoxLib_t * If_NewBoxLibAlloc( void )
{
    If_NewBoxLib_t * pLib = ABC_CALLOC( If_NewBoxLib_t, 1 );
    pLib->vTypes = Vec_PtrAlloc( 16 );
    pLib->vInsts = Vec_PtrAlloc( 16 );
    pLib->tTypeByName = st__init_table( strcmp, st__strhash );
    pLib->tInstByName = st__init_table( strcmp, st__strhash );
    return pLib;
}

void If_NewBoxTypeFree( If_NewBoxType_t * pType )
{
    int i;
    if ( pType == NULL )
        return;
    for ( i = 0; i < pType->nPorts; i++ )
        ABC_FREE( pType->pPorts[i].pName );
    ABC_FREE( pType->pPorts );
    ABC_FREE( pType->pDelays );
    ABC_FREE( pType->pName );
    ABC_FREE( pType );
}

void If_NewBoxInstFree( If_NewBoxInst_t * pInst )
{
    if ( pInst == NULL )
        return;
    ABC_FREE( pInst->pName );
    ABC_FREE( pInst );
}

void If_NewBoxLibFree( If_NewBoxLib_t * pLib )
{
    If_NewBoxType_t * pType;
    If_NewBoxInst_t * pInst;
    int i;
    if ( pLib == NULL )
        return;
    st__free_table( pLib->tTypeByName );
    st__free_table( pLib->tInstByName );
    Vec_PtrForEachEntry( If_NewBoxType_t *, pLib->vTypes, pType, i )
        If_NewBoxTypeFree( pType );
    Vec_PtrForEachEntry( If_NewBoxInst_t *, pLib->vInsts, pInst, i )
        If_NewBoxInstFree( pInst );
    Vec_PtrFree( pLib->vTypes );
    Vec_PtrFree( pLib->vInsts );
    ABC_FREE( pLib );
}

If_NewBoxType_t * If_NewBoxTypeAlloc( char * pName, int Id, If_NewBoxClass_t Class, If_NewBoxKind_t Kind, If_NewBoxColor_t Color, If_NewBoxKeep_t Keep, int nInputs, int nOutputs )
{
    If_NewBoxType_t * pType = ABC_CALLOC( If_NewBoxType_t, 1 );
    pType->pName = If_NewBoxStrsav( pName );
    pType->Id = Id;
    pType->Class = Class;
    pType->Kind = Kind;
    pType->Color = Color;
    pType->Keep = Keep;
    pType->nInputs = nInputs;
    pType->nOutputs = nOutputs;
    pType->nPorts = If_NewBoxPortCount( nInputs, nOutputs );
    pType->pPorts = ABC_CALLOC( If_NewBoxPort_t, pType->nPorts );
    return pType;
}

void If_NewBoxTypeSetPort( If_NewBoxType_t * pType, int iPort, char * pName, If_NewBoxPortRole_t Role, int Width )
{
    assert( pType != NULL );
    assert( iPort >= 0 && iPort < pType->nPorts );
    ABC_FREE( pType->pPorts[iPort].pName );
    pType->pPorts[iPort].pName = If_NewBoxStrsav( pName );
    pType->pPorts[iPort].Role = Role;
    pType->pPorts[iPort].Index = iPort;
    pType->pPorts[iPort].Width = Width;
}

If_NewBoxInst_t * If_NewBoxInstAlloc( char * pName, int Id, If_NewBoxType_t * pType, Abc_Obj_t * pAbcObj )
{
    If_NewBoxInst_t * pInst = ABC_CALLOC( If_NewBoxInst_t, 1 );
    pInst->pName = If_NewBoxStrsav( pName );
    pInst->Id = Id;
    pInst->pType = pType;
    pInst->pAbcObj = pAbcObj;
    pInst->fMappedFromDesign = 1;
    pInst->fPreserve = (pType->Class == IF_NEWBOX_BOX);
    return pInst;
}

If_NewBoxType_t * If_NewBoxLibFindType( If_NewBoxLib_t * pLib, char * pName )
{
    If_NewBoxType_t * pType = NULL;
    if ( pLib == NULL || pName == NULL )
        return NULL;
    if ( !st__lookup( pLib->tTypeByName, pName, (char **)&pType ) )
        return NULL;
    return pType;
}

If_NewBoxInst_t * If_NewBoxLibFindInst( If_NewBoxLib_t * pLib, char * pName )
{
    If_NewBoxInst_t * pInst = NULL;
    if ( pLib == NULL || pName == NULL )
        return NULL;
    if ( !st__lookup( pLib->tInstByName, pName, (char **)&pInst ) )
        return NULL;
    return pInst;
}

If_NewBoxType_t * If_NewBoxLibAddType( If_NewBoxLib_t * pLib, If_NewBoxType_t * pType )
{
    If_NewBoxType_t * pFound;
    assert( pLib != NULL );
    assert( pType != NULL );
    pFound = If_NewBoxLibFindType( pLib, pType->pName );
    if ( pFound != NULL )
        return pFound;
    st__insert( pLib->tTypeByName, pType->pName, (char *)pType );
    Vec_PtrPush( pLib->vTypes, pType );
    return pType;
}

If_NewBoxInst_t * If_NewBoxLibAddInst( If_NewBoxLib_t * pLib, If_NewBoxInst_t * pInst )
{
    If_NewBoxInst_t * pFound;
    assert( pLib != NULL );
    assert( pInst != NULL );
    pFound = If_NewBoxLibFindInst( pLib, pInst->pName );
    if ( pFound != NULL )
        return pFound;
    st__insert( pLib->tInstByName, pInst->pName, (char *)pInst );
    Vec_PtrPush( pLib->vInsts, pInst );
    return pInst;
}

If_NewBoxLib_t * If_NewBoxLibDeriveFromNtk( Abc_Ntk_t * pNtk )
{
    If_NewBoxLib_t * pLib;
    If_NewBoxType_t * pType;
    If_NewBoxInst_t * pInst;
    Abc_Obj_t * pObj;
    char * pTypeName, * pInstName;
    int i, nInputs, nOutputs;
    if ( pNtk == NULL )
        return NULL;
    pLib = If_NewBoxLibAlloc();
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        Abc_Ntk_t * pModel = NULL;
        pTypeName = If_NewBoxDeriveTypeName( pObj );
        pInstName = Abc_ObjName( pObj );
        nInputs = Abc_ObjFaninNum( pObj );
        nOutputs = Abc_ObjFanoutNum( pObj );
        pType = If_NewBoxLibFindType( pLib, pTypeName );
        if ( pType == NULL )
        {
            pType = If_NewBoxTypeAlloc(
                pTypeName,
                Vec_PtrSize(pLib->vTypes),
                If_NewBoxDeriveClass(pObj),
                If_NewBoxDeriveKind(pObj),
                If_NewBoxDeriveColor(pObj),
                If_NewBoxDeriveKeep(pObj),
                nInputs,
                nOutputs
            );
            if ( Abc_ObjIsWhitebox(pObj) )
                pModel = Abc_ObjModel(pObj);
            else if ( Abc_ObjIsBlackbox(pObj) && Abc_ObjData(pObj) != NULL )
                pModel = (Abc_Ntk_t *)Abc_ObjData(pObj);
            if ( pModel )
                If_NewBoxDerivePortsFromModel( pType, pModel );
            else
                If_NewBoxDeriveDefaultPorts( pType );
            If_NewBoxLibAddType( pLib, pType );
        }
        pInst = If_NewBoxInstAlloc( pInstName ? pInstName : pTypeName, Vec_PtrSize(pLib->vInsts), pType, pObj );
        If_NewBoxLibAddInst( pLib, pInst );
    }
    return pLib;
}

void If_NewBoxLibDetach( Abc_Ntk_t * pNtk )
{
    if ( If_NewBoxAttrMan(pNtk) )
        Abc_NtkAttrFree( pNtk, VEC_ATTR_DATA1, 1 );
}

If_NewBoxLib_t * If_NewBoxLibAttach( Abc_Ntk_t * pNtk )
{
    Vec_Att_t * pAttMan;
    If_NewBoxLib_t * pLib;
    If_NewBoxInst_t * pInst;
    int i;
    if ( pNtk == NULL )
        return NULL;
    If_NewBoxLibDetach( pNtk );
    pLib = If_NewBoxLibDeriveFromNtk( pNtk );
    pAttMan = Vec_AttAlloc( Abc_NtkObjNumMax(pNtk) + 1, pLib, (void (*)(void *))If_NewBoxLibFree, NULL, NULL );
    Vec_PtrWriteEntry( pNtk->vAttrs, VEC_ATTR_DATA1, pAttMan );
    Vec_PtrForEachEntry( If_NewBoxInst_t *, pLib->vInsts, pInst, i )
        if ( pInst->pAbcObj )
            Vec_AttWriteEntry( pAttMan, pInst->pAbcObj->Id, pInst );
    return pLib;
}

If_NewBoxLib_t * If_NewBoxLibAttachHierarchy( Abc_Ntk_t * pNtk )
{
    Vec_Att_t * pAttMan;
    If_NewBoxLib_t  * pLib;
    If_NewBoxType_t * pType;
    If_NewBoxInst_t * pInst;
    Abc_Ntk_t * pModel;
    Abc_Obj_t * pObj;
    st__table * tMemo;
    int i, nInputs, nOutputs;
    if ( pNtk == NULL )
        return NULL;
    If_NewBoxLibDetach( pNtk );
    pLib = If_NewBoxLibAlloc();
    tMemo = st__init_table( st__ptrcmp, st__ptrhash );
    Abc_NtkForEachBox( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsBlackbox(pObj) && !Abc_ObjIsWhitebox(pObj) )
            continue;
        pModel = Abc_ObjIsWhitebox(pObj) ? Abc_ObjModel(pObj) : (Abc_Ntk_t *)Abc_ObjData(pObj);
        if ( pModel == NULL )
            continue;
        nInputs = Abc_ObjFaninNum( pObj );
        nOutputs = Abc_ObjFanoutNum( pObj );
        pType = If_NewBoxLibFindType( pLib, Abc_NtkName(pModel) );
        if ( pType == NULL )
        {
            pType = If_NewBoxTypeAlloc(
                Abc_NtkName(pModel),
                Vec_PtrSize(pLib->vTypes),
                IF_NEWBOX_BOX,
                If_NewBoxModelIsSeq_rec( pModel, tMemo ) ? IF_NEWBOX_SEQ : IF_NEWBOX_COMB,
                IF_NEWBOX_BLACK,
                IF_NEWBOX_MUST_KEEP,
                nInputs,
                nOutputs
            );
            If_NewBoxDerivePortsFromModel( pType, pModel );
            If_NewBoxLibAddType( pLib, pType );
        }
        pInst = If_NewBoxInstAlloc( Abc_ObjName(pObj), Vec_PtrSize(pLib->vInsts), pType, pObj );
        pInst->fPreserve = 1;
        pInst->fSelected = 1;
        If_NewBoxLibAddInst( pLib, pInst );
    }
    st__free_table( tMemo );
    pAttMan = Vec_AttAlloc( Abc_NtkObjNumMax(pNtk) + 1, pLib, (void (*)(void *))If_NewBoxLibFree, NULL, NULL );
    Vec_PtrWriteEntry( pNtk->vAttrs, VEC_ATTR_DATA1, pAttMan );
    Vec_PtrForEachEntry( If_NewBoxInst_t *, pLib->vInsts, pInst, i )
        if ( pInst->pAbcObj )
            Vec_AttWriteEntry( pAttMan, pInst->pAbcObj->Id, pInst );
    return pLib;
}

If_NewBoxLib_t * If_NewBoxLibRead( Abc_Ntk_t * pNtk )
{
    Vec_Att_t * pAttMan = If_NewBoxAttrMan( pNtk );
    return pAttMan ? (If_NewBoxLib_t *)Vec_AttMan( pAttMan ) : NULL;
}

If_NewBoxInst_t * If_NewBoxInstFromObj( Abc_Obj_t * pObj )
{
    Vec_Att_t * pAttMan;
    if ( pObj == NULL )
        return NULL;
    pAttMan = If_NewBoxAttrMan( pObj->pNtk );
    return pAttMan ? (If_NewBoxInst_t *)Vec_AttEntry( pAttMan, pObj->Id ) : NULL;
}

void If_NewBoxLibPrint( If_NewBoxLib_t * pLib, FILE * pFile )
{
    If_NewBoxType_t * pType;
    If_NewBoxInst_t * pInst;
    int i;
    if ( pLib == NULL || pFile == NULL )
        return;
    fprintf( pFile, "Box library: %d type(s), %d instance(s)\n", Vec_PtrSize(pLib->vTypes), Vec_PtrSize(pLib->vInsts) );
    Vec_PtrForEachEntry( If_NewBoxType_t *, pLib->vTypes, pType, i )
        fprintf( pFile, "TYPE  %-16s id=%d class=%s kind=%s color=%s keep=%s in=%d out=%d\n",
            pType->pName,
            pType->Id,
            pType->Class == IF_NEWBOX_BOX ? "box" : (pType->Class == IF_NEWBOX_FLOP ? "flop" : "bypass"),
            pType->Kind  == IF_NEWBOX_SEQ   ? "seq"   : "comb",
            pType->Color == IF_NEWBOX_BLACK ? "black" : "white",
            pType->Keep  == IF_NEWBOX_MUST_KEEP ? "keep" : "remove",
            pType->nInputs,
            pType->nOutputs );
    Vec_PtrForEachEntry( If_NewBoxInst_t *, pLib->vInsts, pInst, i )
        fprintf( pFile, "INST  %-16s id=%d type=%s class=%s preserve=%d\n",
            pInst->pName,
            pInst->Id,
            pInst->pType ? pInst->pType->pName : "(null)",
            pInst->pType == NULL ? "(null)" : (pInst->pType->Class == IF_NEWBOX_BOX ? "box" : (pInst->pType->Class == IF_NEWBOX_FLOP ? "flop" : "bypass")),
            pInst->fPreserve );
}

ABC_NAMESPACE_IMPL_END
