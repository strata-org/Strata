namespace Strata

structure Visitor (ASTTy: Type) where
  depthFirstTraveral:
    ∀ {M:Type → Type} [Monad M] {RetTyBegin RetTyEnd:Type},
        -- Called at the beginning of visiting x
        (∀ (x:ASTTy), M RetTyBegin) →
        -- Called at the end of visiting x. Its childrens' outputs are
        -- collected and passed as an argument.
        (∀ (x:ASTTy), RetTyBegin → List RetTyEnd → M RetTyEnd) →
        -- The toplevel module to visit
        ASTTy →
        M retty

namespace BuilderM

/-
  The location of an AST node.
  Given an AST node, its location can be conceptually defined as a list of
  natural numbers describing the indices of the nodes choosing from the root to
  the node. For example. if we have a tree like this:

          A
         / \
        B  C
       / \
      D  E

  The location of node 'E' is [0,1], node 'C' is [1] and 'A' is [].
  This definition has following good properties:
  1. One can pinpoint the exact node from (the full AST, the location).
  2. The parent of a node can be retrieved from the AST using the location.

  However, this definition does not support immutability of locations when
  an AST is updated. For example, if a new node 'F' is inserted between D and E:

          A
         / \
        B  C
      / | \
      D F E

  E's location is [0,2], not [0,1] anymore.
  This can be problematic when we are implementing a worklist-based algorithm,
  e.g., InstCombine in LLVM. In this algorithm, a worklist keeps a list of
  instructions to process, which are (instruction location, the contents). If
  any modification can mutate locations of other nodes, the worklist will have
  wrong locations.

  Another concern is that, when an AST node is overwritten, its old location
  is not invalidated and will silently point to the new overwritten node.

  To resolve this, we use the following solution:
  (1) Wwe allow fractions to the location indices. For example,
      the new F's location will be assigned [0,0.5] and E's location is still
      [0,1].
      This keeps locations of children of a node totally ordered.
      Among other benefits like easier checking of dominance relation in a block,
      this particularly makes debugging easier. :)
  (2) To remember the new fact that '0.5' is assigned to 'F', we introduce
      a new tree called IndexTree. In IndexTree, each node corresponds to
      the AST node and it has a list of 'children indices' as its node data.
      For example, after insertion of 'F', the children indices of 'B' will be
      [0,0.5,1].
  (2) Whenever we want to locate a node from a location, IndexTree is used.

  The updates of IndexTree will be handled automatically by the BuilderM monad.
  The initial construction of IndexTree must be provided by the user
  (TODO: this is something that #strata_gen can provide..!)
-/
def NodeLoc := List (List Nat) /- the inner 'List Nat' mimics fractions -/

inductive IndexTree where
  | node (children: List (
      -- Each child is a pair of (fraction, the subtree).
      (List Nat) × IndexTree))


namespace IndexTree

/-
  Translate a location which has a fraction-based indexing to the original
  natural-number-based indexing.
  Return .none if loc cannot be translated.
-/
def translate (loc:NodeLoc) (itree:IndexTree): Option (List Nat) :=
  match loc, itree with
  | [], _ => .some []
  | h::loc', .node children => do
    let idx <- children.findIdx? (fun (loc2,_) => h == loc2)
    let (_, subtree) <- children[idx]?
    let res <- translate loc' subtree
    return (idx::res)

/-
  Translate a location which has a fraction-based indexing to the original
  natural-number-based indexing, and remove IndexTree that has the location
  erased.
  Return .none if loc cannot be translated.
-/
def erase (loc:NodeLoc) (itree:IndexTree): Option ((List Nat) × IndexTree) :=
  match loc, itree with
  | [], _ => /- cannot remove the root node! -/ .none
  | h::[], .node children => do
    let idx <- children.findIdx? (fun (loc2,_) => h == loc2)
    let children' := children.eraseIdx idx
    return ([idx], .node children')
  | h::loc', .node children => do
    let idx <- children.findIdx? (fun (loc2,_) => h == loc2)
    let (subtreeloc, subtree) <- children[idx]?
    let (transl_res,subtree') <- erase loc' subtree
    let children' := children.set idx (subtreeloc,subtree')
    return (idx::transl_res, .node children')

/-
  Create a fresh NodeLoc after loc as well as the updated IndexTree.
  An empty subtree (.node []) is inserted at the fresh location.
  - The input loc should be a valid location of an AST node.
  - The returned fresh location should not point to any existing AST node.
-/
def freshLocAfter (loc:NodeLoc) (itree:IndexTree)
    : Option (NodeLoc × IndexTree) :=
  match loc, itree with
  | [], _ =>
    -- Cannot create a new location after the root; there must be only one root.
    .none

  | l::[], .node children => do
    let idx <- children.findIdx? (fun (loc2,_) => l == loc2)
    let newloc <- (do
      if idx + 1 == children.length then
        -- If l was, e.g., [4,1] (or "4.1" semantically), return [5] (or "5")
        let ms_digit <- l.head?
        return [ms_digit]
      else
        let (next_loc,_) <- children[idx+1]?
        -- Pick a fresh location between next_loc and l.
        let the_last <- l.getLast?
        let modulo_last := l.dropLast
        let candidate := modulo_last ++ [the_last + 1]
        return (
          if candidate == next_loc then l ++ [1]
          else candidate))
    let children := children.insertIdx idx (newloc,.node [])
    return (newloc::[], .node children)

  | l::l2::t, .node children => do
    let idx <- children.findIdx? (fun (loc2,_) => l == loc2)
    let (subtreeloc,subtree) <- children[idx]?
    let (newloc,newsubtree) <- freshLocAfter (l2::t) subtree
    let children := children.set idx (subtreeloc,newsubtree)
    return (l::newloc, .node children)

end IndexTree


-- The Builder state.
structure State (ASTTy:Type) where
  -- ast: the program that is being updated
  ast: ASTTy
  -- indexTree: the IndexTree for defining program location
  indexTree: IndexTree
  -- insertLoc: new instructions are inserted after this point.
  insertLoc: Option NodeLoc

-- Errors that the Builder monad may throw.
inductive Error where
| empty_location
| invalid_location (loc:NodeLoc)

end BuilderM


-- The definition of a Builder monad :)
abbrev BuilderM (ASTTy:Type) (α:Type) :=
  EStateM BuilderM.Error (BuilderM.State ASTTy) α


namespace BuilderM

instance instMonad ASTTy: Monad (BuilderM ASTTy) :=
  inferInstance

-- Check whether the current insertion location of builder is valid
def checkInsertLoc {ASTTy}: BuilderM ASTTy Unit := do
  let st ← EStateM.get
  match st.insertLoc with
  | .none => return () -- nothing to check
  | .some loc =>
    match st.indexTree.translate loc with
    | .none => throw (.invalid_location loc)
    | .some _ => return ()

-- Get the insertion location.
def getInsertLoc {ASTTy}: BuilderM ASTTy NodeLoc := do
  let st ← EStateM.get
  match st.insertLoc with
  | .none => throw .empty_location
  | .some s => return s

-- Create a new builder. :)
def new {ASTTy} (visitor: Visitor ASTTy) (prog:ASTTy)
                (insertionLoc:Option NodeLoc):
    BuilderM ASTTy Unit :=
  -- Make a fresh IndexTree using the traversal function,
  let visitBegin _: Id Unit := return ()
  let visitEnd _ _ (children_res:List IndexTree): Id IndexTree :=
    return .node (children_res.mapIdx (fun idx a => ([idx],a)))
  let indexTree := visitor.depthFirstTraveral visitBegin visitEnd prog

  do
    EStateM.set {
      ast := prog
      indexTree := indexTree
      insertLoc := insertionLoc
    }
    checkInsertLoc

def setInsertionPoint {ProgTy} (insertLoc:Option NodeLoc):
    BuilderM ProgTy Unit := do
  EStateM.modifyGet (fun x => ((), { x with insertLoc := insertLoc }))
  checkInsertLoc

end BuilderM
