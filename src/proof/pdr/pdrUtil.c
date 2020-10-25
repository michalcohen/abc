/**CFile****************************************************************

  FileName    [pdrUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrUtil.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"
#include "stdbool.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
// region set related functions
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetAlloc( int nSize )
{
    Pdr_Set_t * p;
    assert( nSize >= 0 && nSize < (1<<30) );
    p = (Pdr_Set_t *)ABC_CALLOC( char, sizeof(Pdr_Set_t) + nSize * sizeof(int) );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetCreate( Vec_Int_t * vLits, Vec_Int_t * vPiLits )
{
    Pdr_Set_t * p;
    int i;
    assert( Vec_IntSize(vLits) + Vec_IntSize(vPiLits) < (1<<30) );
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + (Vec_IntSize(vLits) + Vec_IntSize(vPiLits)) * sizeof(int) );
    p->nLits  = Vec_IntSize(vLits);
    p->nTotal = Vec_IntSize(vLits) + Vec_IntSize(vPiLits);
    p->nRefs  = 1;
    p->Sign   = 0;
    for ( i = 0; i < p->nLits; i++ )
    {
        p->Lits[i] = Vec_IntEntry(vLits, i);
        p->Sign   |= ((word)1 << (p->Lits[i] % 63));
    }
    Vec_IntSelectSort( p->Lits, p->nLits );
    // remember PI literals 
    for ( i = p->nLits; i < p->nTotal; i++ )
        p->Lits[i] = Vec_IntEntry(vPiLits, i-p->nLits);
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetCreateFrom( Pdr_Set_t * pSet, int iRemove )
{
    Pdr_Set_t * p;
    int i, k = 0;
    assert( iRemove >= 0 && iRemove < pSet->nLits );
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + (pSet->nTotal - 1) * sizeof(int) );
    p->nLits  = pSet->nLits - 1;
    p->nTotal = pSet->nTotal - 1;
    p->nRefs  = 1;
    p->Sign   = 0;
    for ( i = 0; i < pSet->nTotal; i++ )
    {
        if ( i == iRemove )
            continue;
        p->Lits[k++] = pSet->Lits[i];
        if ( i >= pSet->nLits )
            continue;
        p->Sign   |= ((word)1 << (pSet->Lits[i] % 63));
    }
    assert( k == p->nTotal );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetCreateSubset( Pdr_Set_t * pSet, int * pLits, int nLits )
{
    Pdr_Set_t * p;
    int i, k = 0;
    assert( nLits >= 0 && nLits <= pSet->nLits );
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + (nLits + pSet->nTotal - pSet->nLits) * sizeof(int) );
    p->nLits  = nLits;
    p->nTotal = nLits + pSet->nTotal - pSet->nLits;
    p->nRefs  = 1;
    p->Sign   = 0;
    for ( i = 0; i < nLits; i++ )
    {
        assert( pLits[i] >= 0 );
        p->Lits[k++] = pLits[i];
        p->Sign   |= ((word)1 << (pLits[i] % 63));
    }
    Vec_IntSelectSort( p->Lits, p->nLits );
    for ( i = pSet->nLits; i < pSet->nTotal; i++ )
        p->Lits[k++] = pSet->Lits[i];
    assert( k == p->nTotal );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetDup( Pdr_Set_t * pSet )
{
    Pdr_Set_t * p;
    int i;
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + pSet->nTotal * sizeof(int) );
    p->nLits  = pSet->nLits;
    p->nTotal = pSet->nTotal;
    p->nRefs  = 1;
    p->Sign   = pSet->Sign;
    for ( i = 0; i < pSet->nTotal; i++ )
        p->Lits[i] = pSet->Lits[i];
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetRef( Pdr_Set_t * p )
{
    p->nRefs++;
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_SetDeref( Pdr_Set_t * p )
{
    if ( --p->nRefs == 0 )
        ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_SetPrint( FILE * pFile, Pdr_Set_t * p, int nRegs, Vec_Int_t * vFlopCounts )
{
    char * pBuff;
    int i, k, Entry;
    pBuff = ABC_ALLOC( char, nRegs + 1 );
    for ( i = 0; i < nRegs; i++ )
        pBuff[i] = '-';
    pBuff[i] = 0;
    for ( i = 0; i < p->nLits; i++ )
    {
        if ( p->Lits[i] == -1 )
            continue;
        pBuff[Abc_Lit2Var(p->Lits[i])] = (Abc_LitIsCompl(p->Lits[i])? '0':'1');
    }
    if ( vFlopCounts )
    {
        // skip some literals
        k = 0;
        Vec_IntForEachEntry( vFlopCounts, Entry, i )
            if ( Entry ) 
                pBuff[k++] = pBuff[i];
        pBuff[k] = 0;
    }
    fprintf( pFile, "%s", pBuff );
    ABC_FREE( pBuff );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ZPdr_SetPrint( Pdr_Set_t * p )
{
    int i;
    for ( i = 0; i < p->nLits; i++)
        printf ("%d ", p->Lits[i]);
    printf ("\n");

}

/**Function*************************************************************

  Synopsis    [Return the intersection of p1 and p2.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * ZPdr_SetIntersection( Pdr_Set_t * p1, Pdr_Set_t * p2, Hash_Int_t * keep )
{
    Pdr_Set_t * pIntersection;
    Vec_Int_t * vCommonLits, * vPiLits;
    int i, j, nLits;
    nLits = p1->nLits;
    if ( p2->nLits < nLits )
        nLits = p2->nLits;
    vCommonLits = Vec_IntAlloc( nLits );
    vPiLits = Vec_IntAlloc( 1 );
    for ( i = 0, j = 0; i < p1->nLits && j < p2->nLits; )
    {
        if ( p1->Lits[i] > p2->Lits[j] )
        {
            if ( Hash_IntExists( keep, p2->Lits[j] ) )
            {
                //about to drop a literal that should not be dropped
                Vec_IntFree( vCommonLits );
                Vec_IntFree( vPiLits );
                return NULL;
            }
            j++;
        }
        else if ( p1->Lits[i] < p2->Lits[j] )
        {
            if ( Hash_IntExists( keep, p1->Lits[i] ) )
            {
                //about to drop a literal that should not be dropped
                Vec_IntFree( vCommonLits );
                Vec_IntFree( vPiLits );
                return NULL;
            }
            i++;
        }
        else
        {
          Vec_IntPush( vCommonLits, p1->Lits[i] );
          i++;
          j++;
        }
    }
    pIntersection = Pdr_SetCreate( vCommonLits, vPiLits );
    Vec_IntFree( vCommonLits );
    Vec_IntFree( vPiLits );
    return pIntersection;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_SetPrintStr( Vec_Str_t * vStr, Pdr_Set_t * p, int nRegs, Vec_Int_t * vFlopCounts )
{
    char * pBuff;
    int i, k = 0, Entry;
    pBuff = ABC_ALLOC( char, nRegs + 1 );
    for ( i = 0; i < nRegs; i++ )
        pBuff[i] = '-';
    pBuff[i] = 0;
    for ( i = 0; i < p->nLits; i++ )
    {
        if ( p->Lits[i] == -1 )
            continue;
        pBuff[Abc_Lit2Var(p->Lits[i])] = (Abc_LitIsCompl(p->Lits[i])? '0':'1');
    }
    if ( vFlopCounts )
    {
        // skip some literals
        Vec_IntForEachEntry( vFlopCounts, Entry, i )
            if ( Entry ) 
                pBuff[k++] = pBuff[i];
        pBuff[k] = 0;
    }
    Vec_StrPushBuffer( vStr, pBuff, k );
    Vec_StrPush( vStr, ' ' );
    Vec_StrPush( vStr, '1' );
    Vec_StrPush( vStr, '\n' );
    ABC_FREE( pBuff );
}

/**Function*************************************************************

  Synopsis    [Return 1 if pOld set-theoretically contains pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_SetContains( Pdr_Set_t * pOld, Pdr_Set_t * pNew )
{
    int * pOldInt, * pNewInt;
    assert( pOld->nLits > 0 );
    assert( pNew->nLits > 0 );
    if ( pOld->nLits < pNew->nLits )
        return 0;
    if ( (pOld->Sign & pNew->Sign) != pNew->Sign )
        return 0;
    pOldInt = pOld->Lits + pOld->nLits - 1;
    pNewInt = pNew->Lits + pNew->nLits - 1;
    while ( pNew->Lits <= pNewInt )
    {
        if ( pOld->Lits > pOldInt )
            return 0;
        assert( *pNewInt != -1 );
        assert( *pOldInt != -1 );
        if ( *pNewInt == *pOldInt )
            pNewInt--, pOldInt--;
        else if ( *pNewInt < *pOldInt )
            pOldInt--;
        else
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Return 1 if pOld set-theoretically contains pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_SetContainsSimple( Pdr_Set_t * pOld, Pdr_Set_t * pNew )
{
    int * pOldInt, * pNewInt;
    assert( pOld->nLits > 0 );
    assert( pNew->nLits > 0 );
    pOldInt = pOld->Lits + pOld->nLits - 1;
    pNewInt = pNew->Lits + pNew->nLits - 1;
    while ( pNew->Lits <= pNewInt )
    {
        assert( *pOldInt != -1 );
        if ( *pNewInt == -1 )
        {
            pNewInt--;
            continue;
        }
        if ( pOld->Lits > pOldInt )
            return 0;
        assert( *pNewInt != -1 );
        assert( *pOldInt != -1 );
        if ( *pNewInt == *pOldInt )
            pNewInt--, pOldInt--;
        else if ( *pNewInt < *pOldInt )
            pOldInt--;
        else
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Return 1 if the state cube contains init state (000...0).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_SetIsInit( Pdr_Set_t * pCube, int iRemove )
{
    int i;
    for ( i = 0; i < pCube->nLits; i++ )
    {
        assert( pCube->Lits[i] != -1 );
        if ( i == iRemove )
            continue;
        if ( Abc_LitIsCompl( pCube->Lits[i] ) == 0 )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_SetCompare( Pdr_Set_t ** pp1, Pdr_Set_t ** pp2 )
{
    Pdr_Set_t * p1 = *pp1;
    Pdr_Set_t * p2 = *pp2;
    int i;
    for ( i = 0; i < p1->nLits && i < p2->nLits; i++ )
    {
        if ( p1->Lits[i] > p2->Lits[i] )
            return -1;
        if ( p1->Lits[i] < p2->Lits[i] )
            return 1;
    }
    if ( i == p1->nLits && i < p2->nLits )
        return -1;
    if ( i < p1->nLits && i == p2->nLits )
        return 1;
    return 0;
}

// endregion

// region obligation related functions
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_OblStart( int k, int prio, Pdr_Set_t * pState, Pdr_Obl_t * pNext )
{
    Pdr_Obl_t * p;
    p = ABC_ALLOC( Pdr_Obl_t, 1 );
    p->iFrame = k;
    p->prio   = prio;
    p->nRefs  = 1;
    p->pState = pState;
    p->pNext  = pNext;
    p->pLink  = NULL;
    return p;    
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_OblRef( Pdr_Obl_t * p )
{
    p->nRefs++;
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_OblDeref( Pdr_Obl_t * p )
{
    if ( --p->nRefs == 0 )
    {
        if ( p->pNext )
            Pdr_OblDeref( p->pNext );
        Pdr_SetDeref( p->pState );
        ABC_FREE( p );
    }
}

// endregion

// region queue related functions
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_QueueIsEmpty( Pdr_Man_t * p )
{
    return p->pQueue == NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_QueueHead( Pdr_Man_t * p )
{
    return p->pQueue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_QueuePop( Pdr_Man_t * p )
{
    Pdr_Obl_t * pRes = p->pQueue;
    if ( p->pQueue == NULL )
        return NULL;
    p->pQueue = p->pQueue->pLink;
    Pdr_OblDeref( pRes );
    p->nQueCur--;
    return pRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_QueueClean( Pdr_Man_t * p )
{
    Pdr_Obl_t * pThis;
    while ( (pThis = Pdr_QueuePop(p)) )
        Pdr_OblDeref( pThis );
    pThis = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_QueuePush( Pdr_Man_t * p, Pdr_Obl_t * pObl )
{
    Pdr_Obl_t * pTemp, ** ppPrev;
    p->nObligs++;
    p->nQueCur++;
    p->nQueMax = Abc_MaxInt( p->nQueMax, p->nQueCur );
    Pdr_OblRef( pObl );
    if ( p->pQueue == NULL )
    {
        p->pQueue = pObl;
        return;
    }
    for ( ppPrev = &p->pQueue, pTemp = p->pQueue; pTemp; ppPrev = &pTemp->pLink, pTemp = pTemp->pLink )
        if ( pTemp->iFrame > pObl->iFrame || (pTemp->iFrame == pObl->iFrame && pTemp->prio > pObl->prio) )
            break;
    *ppPrev = pObl;
    pObl->pLink = pTemp;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_QueuePrint( Pdr_Man_t * p )
{
    Pdr_Obl_t * pObl;
    for ( pObl = p->pQueue; pObl; pObl = pObl->pLink )
        Abc_Print( 1, "Frame = %2d.  Prio = %8d.\n", pObl->iFrame, pObl->prio );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_QueueStop( Pdr_Man_t * p )
{
    Pdr_Obl_t * pObl;
    while ( !Pdr_QueueIsEmpty(p) )
    {
        pObl = Pdr_QueuePop(p);
        Pdr_OblDeref( pObl );
    }
    p->pQueue = NULL;
    p->nQueCur = 0;
}
// endregion

// region graph related function

Pdr_ListNodePred * Pdr_ListNodePredStart(Pdr_TreeNode * tn){
    Pdr_ListNodePred * ln = ABC_ALLOC(Pdr_ListNodePred, 1);
    ln->tree_node = Pdr_TreeNodeRef(tn);
    ln->next = NULL;
    return ln;
}

Pdr_TreeNode * Pdr_TreeNodeStart( Pdr_Set_t * pState, Pdr_TreeNode * pSucc )
{
    Pdr_TreeNode * tn;
    tn = ABC_ALLOC( Pdr_TreeNode, 1 );


    tn->nRefs  = 1;
    tn->pState = Pdr_SetRef(pState);
    tn->pSucc  = Pdr_TreeNodeRef(pSucc);
    tn->pPred  = NULL;
    if (pSucc)
    {
        Pdr_ListNodePred * pred = Pdr_ListNodePredStart(tn);
        if (pSucc->pPred){
            pred->next = pSucc->pPred;
            pSucc->pPred = pred;
        } else {
            pSucc->pPred = pred;
        }
    }

    return tn;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_TreeNode * Pdr_TreeNodeRef( Pdr_TreeNode * tn )
{
    if ( !tn ){
        return NULL;
    }
    tn->nRefs++;
    return tn;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_TreeNodeDeref( Pdr_TreeNode * tn )
{
    if ( --tn->nRefs == 0 )
    {
        if ( tn->pSucc )
            Pdr_TreeNodeDeref( tn->pSucc );

        for (Pdr_ListNodePred * p = tn->pPred; p;  p = p->next){
           Pdr_TreeNodeDeref(p->tree_node);
        }
        Pdr_SetDeref( tn->pState );
        ABC_FREE( tn );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_TreeIsEmpty( Pdr_Tree * t )
{
    return t == NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_TreeNode * Pdr_GetTreeRoot( Pdr_Tree * t )
{
    return t->root;
}


void _Pdr_TreeClean_Helper( Pdr_TreeNode * tn )
{
    if ( !tn ){
        return;
    }
    for ( Pdr_ListNodePred * pPred = tn->pPred; pPred; )
    {
        _Pdr_TreeClean_Helper(pPred->tree_node);
        Pdr_ListNodePred * tmp = pPred;
        pPred = pPred->next;
        ABC_FREE( tmp );
    }
    Pdr_SetDeref( tn->pState );
    ABC_FREE( tn );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_TreeClean( Pdr_Tree * t )
{
    Pdr_TreePrint( t->root, 0 );
    fflush(stdout);
    _Pdr_TreeClean_Helper(t->root);
    ABC_FREE( t );
}

Pdr_TreeNode * Pdr_TreeFindNode(Pdr_TreeNode * current, Pdr_Set_t * state){
    if ( ! current ){
        return NULL;
    }
    if (current->pState == state){
        return current;
    }
    for (Pdr_ListNodePred * p = current->pPred; p; p = p->next){
        Pdr_TreeNode * res = Pdr_TreeFindNode(p->tree_node, state);
        if ( res ){
            return res;
        }
    }
    return NULL;
}
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_TreeInsert( Pdr_Tree * t, Pdr_Set_t * state, Pdr_Set_t * succ )
{
    // maybe assert?
    if (Pdr_TreeFindNode(t->root, state)){
        return;
    }
    Pdr_TreeNode * tn_succ = Pdr_TreeFindNode(t->root, succ);
    Pdr_TreeNode * tn_state = Pdr_TreeNodeStart(state, tn_succ);
    if ( ! t->root ){
        t->root = tn_state;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_TreePrint( Pdr_TreeNode * tn, int level )
{
    if ( !tn ){
        return;
    }
    for (int i = 0; i < level; i++) {

        printf("\t");
    }

    printf("%p", tn->pState);
    // Pdr_SetPrint( FILE * pFile, Pdr_Set_t * p, int nRegs, Vec_Int_t * vFlopCounts )
    if ( !tn->pPred ) return;
    for (Pdr_ListNodePred * pred = tn->pPred; pred; pred = pred->next) {
        printf("\n");
        Pdr_TreePrint(pred->tree_node, level + 1);
    }
}

Pdr_Tree * Pdr_TreeStart(){
    Pdr_Tree * t;
    t = ABC_ALLOC( Pdr_Tree, 1 );
    t->root = NULL;
}


// endregion

// region CubeHashTable
Pdr_CubeTable * Pdr_CubeTableStart(){
    Pdr_CubeTable * t;
    t = ABC_ALLOC( Pdr_CubeTable, 1 );
    t->first = NULL;
}

Pdr_CubeTableNode * Pdr_CubeTableNodeStart(Pdr_Set_t * state){
    Pdr_CubeTableNode  * n = ABC_ALLOC(Pdr_CubeTableNode, 1);
    n->pState = state;
    Pdr_SetRef(state);
    n->next = NULL;
    n->countRef = 1;
}

void Pdr_CubeTableInsert(Pdr_CubeTable * t, Pdr_CubeTableNode * c){
    if (!t->first){
        t->first = c;
    } else {
        c->next = t->first;
        t->first = c;
    }
}

bool Are_states_identical(Pdr_Set_t * first, Pdr_Set_t * second){
    if (first == second) {
        return true; // They are the same object
    }
    if (first->nLits != second->nLits){
        return false; // They have different amount of literals
    }
    for (int i = 0; i < first->nLits; i++){
        if (first->Lits[i] != second->Lits[i]){
            return false;
        }
    }
    return true;
}

Pdr_CubeTableNode * Pdr_CubeTableFindNode(Pdr_CubeTableNode * current, Pdr_Set_t * state){
    if ( ! current ){
        return NULL;
    }
    if (Are_states_identical(current->pState, state)){
        return current;
    }
    return Pdr_CubeTableFindNode(current->next, state);
}

void Pdr_CubeTableUpdate( Pdr_CubeTable * t, Pdr_Set_t * state)
{
    Pdr_CubeTableNode * ctn = Pdr_CubeTableFindNode(t->first, state);
    if ( ctn ){
        ctn->countRef++;
    } else {
        Pdr_CubeTableInsert(t, Pdr_CubeTableNodeStart(state));
    }

}
// endregion


#define PDR_VAL0  1
#define PDR_VAL1  2
#define PDR_VALX  3

/**Function*************************************************************

  Synopsis    [Returns value (0 or 1) or X if unassigned.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr_ObjSatValue( Aig_Man_t * pAig, Aig_Obj_t * pNode, int fCompl )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pNode) )
        return (pNode->fMarkA ^ fCompl) ? PDR_VAL1 : PDR_VAL0;
    return PDR_VALX;
}

/**Function*************************************************************

  Synopsis    [Recursively searched for a satisfying assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_NtkFindSatAssign_rec( Aig_Man_t * pAig, Aig_Obj_t * pNode, int Value, Pdr_Set_t * pCube, int Heur )
{
    int Value0, Value1;
    if ( Aig_ObjIsConst1(pNode) )
        return 1;
    if ( Aig_ObjIsTravIdCurrent(pAig, pNode) )
        return ((int)pNode->fMarkA == Value);
    Aig_ObjSetTravIdCurrent(pAig, pNode);
    pNode->fMarkA = Value;
    if ( Aig_ObjIsCi(pNode) )
    {
        if ( Saig_ObjIsLo(pAig, pNode) )
        {
//            pCube->Lits[pCube->nLits++] = Abc_Var2Lit( Aig_ObjCioId(pNode) - Saig_ManPiNum(pAig), !Value );
            pCube->Lits[pCube->nLits++] = Abc_Var2Lit( Aig_ObjCioId(pNode) - Saig_ManPiNum(pAig), Value );
            pCube->Sign |= ((word)1 << (pCube->Lits[pCube->nLits-1] % 63));
        }
        return 1;
    }
    assert( Aig_ObjIsNode(pNode) );
    // propagation
    if ( Value ) 
    {
        if ( !Pdr_NtkFindSatAssign_rec(pAig, Aig_ObjFanin0(pNode), !Aig_ObjFaninC0(pNode), pCube, Heur) )
            return 0;
        return Pdr_NtkFindSatAssign_rec(pAig, Aig_ObjFanin1(pNode), !Aig_ObjFaninC1(pNode), pCube, Heur);
    }
    // justification
    Value0 = Pdr_ObjSatValue( pAig, Aig_ObjFanin0(pNode), Aig_ObjFaninC0(pNode) );
    if ( Value0 == PDR_VAL0 )
        return 1;
    Value1 = Pdr_ObjSatValue( pAig, Aig_ObjFanin1(pNode), Aig_ObjFaninC1(pNode) );
    if ( Value1 == PDR_VAL0 )
        return 1;
    if ( Value0 == PDR_VAL1 && Value1 == PDR_VAL1 )
        return 0;
    if ( Value0 == PDR_VAL1 )
        return Pdr_NtkFindSatAssign_rec(pAig, Aig_ObjFanin1(pNode), Aig_ObjFaninC1(pNode), pCube, Heur);
    if ( Value1 == PDR_VAL1 )
        return Pdr_NtkFindSatAssign_rec(pAig, Aig_ObjFanin0(pNode), Aig_ObjFaninC0(pNode), pCube, Heur);
    assert( Value0 == PDR_VALX && Value1 == PDR_VALX );
    // decision making
//    if ( rand() % 10 == Heur )
    if ( Aig_ObjId(pNode) % 4 == Heur )
        return Pdr_NtkFindSatAssign_rec(pAig, Aig_ObjFanin1(pNode), Aig_ObjFaninC1(pNode), pCube, Heur);
    else
        return Pdr_NtkFindSatAssign_rec(pAig, Aig_ObjFanin0(pNode), Aig_ObjFaninC0(pNode), pCube, Heur);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



// [@Michal]
void Pdr_Write_to_stats(Pdr_Man_t * p, const char * format, ...){
    int max_path_size = 200;
    va_list args;
    va_start(args, format);
    char cwd[max_path_size];
    memset(cwd, 0, max_path_size);
    strcat(cwd, "./");
    strcat(cwd, p->pAig->pName);
    strcat(cwd, "_");
    strcat(cwd, "stats_michal.csv");
    FILE *fp = fopen(cwd, "a+");
    vfprintf(fp, format, args);
    fclose(fp);
}

void Pdr_Initi_wrtie_to_stats(Pdr_Man_t * p){
    int blooop = 5;
    int max_path_size = 200;
    char cwd[max_path_size];
    memset(cwd, 0, max_path_size);
    strcat(cwd, "./");
    strcat(cwd, p->pAig->pName);
    strcat(cwd, "_");
    strcat(cwd, "stats_michal.csv");
    FILE *fp = fopen(cwd, "w+");
    fprintf(fp, "level,cube,depth\n");
    fclose(fp);
}
ABC_NAMESPACE_IMPL_END

