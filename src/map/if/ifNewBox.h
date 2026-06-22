#ifndef ABC__map__if__ifNewBox_h
#define ABC__map__if__ifNewBox_h

#include "stdio.h"
#include "misc/vec/vec.h"
#include "misc/st/st.h"

ABC_NAMESPACE_HEADER_START

typedef struct Abc_Ntk_t_ Abc_Ntk_t;
typedef struct Abc_Obj_t_ Abc_Obj_t;

typedef enum {
    IF_NEWBOX_COMB = 0,
    IF_NEWBOX_SEQ  = 1
} If_NewBoxKind_t;

typedef enum {
    IF_NEWBOX_WHITE = 0,
    IF_NEWBOX_BLACK = 1
} If_NewBoxColor_t;

typedef enum {
    IF_NEWBOX_CAN_REMOVE = 0,
    IF_NEWBOX_MUST_KEEP  = 1
} If_NewBoxKeep_t;

typedef enum {
    IF_NEWBOX_BOX = 0,
    IF_NEWBOX_FLOP,
    IF_NEWBOX_BYPASS
} If_NewBoxClass_t;

typedef enum {
    IF_NEWBOX_PORT_IN  = 0,
    IF_NEWBOX_PORT_OUT = 1,
    IF_NEWBOX_PORT_CLK = 2,
    IF_NEWBOX_PORT_RST = 3,
    IF_NEWBOX_PORT_EN  = 4
} If_NewBoxPortRole_t;

typedef struct If_NewBoxPort_t_ If_NewBoxPort_t;
typedef struct If_NewBoxType_t_ If_NewBoxType_t;
typedef struct If_NewBoxInst_t_ If_NewBoxInst_t;
typedef struct If_NewBoxLib_t_  If_NewBoxLib_t;

struct If_NewBoxPort_t_
{
    char *               pName;
    If_NewBoxPortRole_t  Role;
    int                  Index;
    int                  Width;
};

struct If_NewBoxType_t_
{
    char *               pName;
    int                  Id;
    If_NewBoxClass_t     Class;
    If_NewBoxKind_t      Kind;
    If_NewBoxColor_t     Color;
    If_NewBoxKeep_t      Keep;
    int                  nInputs;
    int                  nOutputs;
    int                  nPorts;
    If_NewBoxPort_t *    pPorts;
    int                  fHasTiming;
    int *                pDelays;
    void *               pUser;
};

struct If_NewBoxInst_t_
{
    char *               pName;
    int                  Id;
    If_NewBoxType_t *    pType;
    Abc_Obj_t *          pAbcObj;
    int                  fMappedFromDesign;
    int                  fPreserve;
    int                  fSelected;
    void *               pUser;
};

struct If_NewBoxLib_t_
{
    Vec_Ptr_t *          vTypes;
    Vec_Ptr_t *          vInsts;
    st__table *          tTypeByName;
    st__table *          tInstByName;
};

extern If_NewBoxLib_t *  If_NewBoxLibAlloc( void );
extern void              If_NewBoxLibFree( If_NewBoxLib_t * pLib );
extern If_NewBoxType_t * If_NewBoxTypeAlloc( char * pName, int Id, If_NewBoxClass_t Class, If_NewBoxKind_t Kind, If_NewBoxColor_t Color, If_NewBoxKeep_t Keep, int nInputs, int nOutputs );
extern void              If_NewBoxTypeFree( If_NewBoxType_t * pType );
extern void              If_NewBoxTypeSetPort( If_NewBoxType_t * pType, int iPort, char * pName, If_NewBoxPortRole_t Role, int Width );
extern If_NewBoxInst_t * If_NewBoxInstAlloc( char * pName, int Id, If_NewBoxType_t * pType, Abc_Obj_t * pAbcObj );
extern void              If_NewBoxInstFree( If_NewBoxInst_t * pInst );
extern If_NewBoxType_t * If_NewBoxLibAddType( If_NewBoxLib_t * pLib, If_NewBoxType_t * pType );
extern If_NewBoxInst_t * If_NewBoxLibAddInst( If_NewBoxLib_t * pLib, If_NewBoxInst_t * pInst );
extern If_NewBoxType_t * If_NewBoxLibFindType( If_NewBoxLib_t * pLib, char * pName );
extern If_NewBoxInst_t * If_NewBoxLibFindInst( If_NewBoxLib_t * pLib, char * pName );
extern If_NewBoxLib_t *  If_NewBoxLibDeriveFromNtk( Abc_Ntk_t * pNtk );
extern If_NewBoxLib_t *  If_NewBoxLibAttach( Abc_Ntk_t * pNtk );
extern If_NewBoxLib_t *  If_NewBoxLibAttachHierarchy( Abc_Ntk_t * pNtk );
extern void              If_NewBoxLibDetach( Abc_Ntk_t * pNtk );
extern If_NewBoxLib_t *  If_NewBoxLibRead( Abc_Ntk_t * pNtk );
extern If_NewBoxInst_t * If_NewBoxInstFromObj( Abc_Obj_t * pObj );
extern void              If_NewBoxLibPrint( If_NewBoxLib_t * pLib, FILE * pFile );

ABC_NAMESPACE_HEADER_END

#endif
