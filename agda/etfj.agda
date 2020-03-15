open import Data.Nat
open import Data.Product
open import Data.List using (List; []; _∷_; _++_; unzip)
open import Data.List.All using (All; _∷_; [])
open import Data.List.Any using (here; there)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)

module etfj (Obj : ℕ)  where

  Name : Set
  Name = ℕ

  Ctx : Set
  Ctx = List (Name × Name)

  data _∋_∶_ {A : Set} : List (Name × A) → Name → A → Set where
    here  : ∀ {Δ x d} → ((x , d) ∷ Δ) ∋ x ∶ d
    there : ∀ {Δ x y d₁ d₂} → Δ ∋ x ∶ d₁ → ((y , d₂) ∷ Δ) ∋ x ∶ d₁

  data interl {A : Set} {B : Set} : List (Name × A) → List B → List (Name × B) → Set where
    here  : interl [] [] [] 
    there : ∀ {x a b nas bs bns}
         → interl nas bs bns
         → interl ((x , a) ∷ nas) (b ∷ bs) ((x , b) ∷ bns)

  module Syntax where

    data Expr : Set where
      Var   : Name → Expr
      Field : Expr → Name → Expr
      Invk  : Expr → Name → List Expr → Expr
      New   : Name → List Expr → Expr

    data Val : Expr → Set where
      V-New : ∀ {c cp} → All Val cp → Val (New c cp)

  open Syntax

  module ClassTable where
    
    record Meth : Set where
      field
        ret    : Name
        params : List (Name × Name)
        body   : Expr

    record Class : Set where
      constructor ClassDef
      field
        cname  : Name
        super  : Name
        flds   : List (Name × Name)
        meths  : List (Name × Meth)

    CT : Set
    CT = List (Name × Class)

  open ClassTable

  module Auxiliary (Δ : CT) where

    data fields : Name → List (Name × Name) → Set where
      obj   : fields Obj []
      other : ∀ {c cd sf}
           → Δ ∋ c ∶ cd
           → fields (Class.super cd) sf
           → fields c (sf ++ Class.flds cd)

    data method : Name → Name → Meth → Set where
      this  : ∀ {c cd m mdecl}
           → Δ ∋ c ∶ cd
           → (Class.meths cd) ∋ m ∶ mdecl
           → method c m mdecl
--      super : ∀ {c cd m mdecl}
--           → Δ ∋ c ∶ cd
--           → method (Class.super cd) m mdecl
--           → method c m mdecl

    -- Subtyping

    data subtyping : Name → Name → Set where
      refl    : ∀ {c}       → subtyping c c
      extends : ∀ {c d f m} → Δ ∋ c ∶ (ClassDef c d f m) → subtyping c d
      trans   : ∀ {c d e}   → subtyping c d → subtyping d e → subtyping c e


  -- Small step relation
  
  module Eval (Δ : CT) where

    open Auxiliary Δ
  
    subs : Expr → List (Name × Expr) → Expr
    subs-list : List Expr → List (Name × Expr) → List Expr

    subs (Var x) [] = Var x
    subs (Var x) ((y , e) ∷ l) with x ≟ y
    ... | yes refl = e
    ... | no _ = subs (Var x) l
    subs (Field e f) l = Field (subs e l) f
    subs (Invk e m mp) l = Invk (subs e l) m (subs-list mp l)
    subs (New c cp) l = New c (subs-list cp l)

    subs-list [] l = []
    subs-list (e ∷ el) l = subs e l ∷ subs-list el l
      
    infix 4 _⟶_
    infix 4 _↦_

    data _⟶_ : Expr → Expr → Set 
    data _↦_ : List Expr → List Expr → Set 

    data _⟶_ where
      R-Field     : ∀ {C cp flds f fi fes}
                 → fields C flds
                 → interl flds cp fes
                 → fes ∋ f ∶ fi
                 → Field (New C cp) f ⟶ fi
      RC-Field    : ∀ {e e' f}
                 → e ⟶ e'
                 → Field e f ⟶ Field e' f
      R-Invk      : ∀ {C cp m MD ap ep}
                 → method C m MD
                 → interl (Meth.params MD) ap ep
                 → Invk (New C cp) m ap ⟶ subs (Meth.body MD) ep
      RC-InvkRecv : ∀ {e e' m mp}
                 → e ⟶ e'
                 → Invk e m mp ⟶ Invk e' m mp
      RC-InvkArg  : ∀ {e m mp mp'}
                 → mp ↦ mp'
                 → Invk e m mp ⟶ Invk e m mp'
      RC-NewArg   : ∀ {C cp cp'}
                 → cp ↦ cp'
                 → New C cp ⟶ New C cp'

    data _↦_ where
      here  : ∀ {e e' l} → e ⟶ e' → e ∷ l ↦ e' ∷ l
      there : ∀ {e l l'} → l ↦ l' → e ∷ l ↦ e ∷ l'

  module Typing (Δ : CT) where

    open Auxiliary Δ

    -- Expression typing

    infix 4 _⊢_∶_
    infix 4 _⊧_∶_
    data _⊢_∶_ : Ctx → Expr → Name → Set
    data _⊧_∶_ : Ctx → List Expr → List Name → Set

    data _⊢_∶_ where
      T-Var   : ∀ {Γ x C}
             → Γ ∋ x ∶ C
             → Γ ⊢ (Var x) ∶ C
      T-Field : ∀ {Γ C Ci e f flds}
             → Γ ⊢ e ∶ C
             → fields C flds
             → flds ∋ f ∶ Ci
             → Γ ⊢ (Field e f) ∶ Ci
      T-Invk  : ∀ {Γ C e m MD mp}
             → Γ ⊢ e ∶ C
             → method C m MD
             → Γ ⊧ mp ∶ proj₂ (unzip (Meth.params MD))
             → Γ ⊢ (Invk e m mp) ∶ (Meth.ret MD)
      T-New   : ∀ {Γ C cp flds}
             → fields C flds
             → Γ ⊧ cp ∶ proj₂ (unzip flds)
             → Γ ⊢ (New C cp) ∶ C

    data _⊧_∶_ where
      here  : ∀ {Γ}
           → Γ ⊧ [] ∶ []
      there : ∀ {Γ e C l Cl}
           → Γ ⊢ e ∶ C
           → Γ ⊧ l ∶ Cl
           → Γ ⊧ e ∷ l ∶ C ∷ Cl

    -- Method typing

    data MethodOk : Class → Meth → Set where
      T-Method : ∀ {CD MD}
              → Meth.params MD ⊢ Meth.body MD ∶ Meth.ret MD
              → MethodOk CD MD

    -- Class typing

    data ClassOk : Class → Set where
      T-Class : ∀ {CD}
             → All (MethodOk CD) (proj₂ (unzip (Class.meths CD)))
             → ClassOk CD

    -- Class table typing

    CTOk : CT → Set
    CTOk Δ = All (λ ci → ClassOk (proj₂ ci)) Δ

  module AuxiliaryLemmas (Δ : CT) where

    open Typing Δ
    open Auxiliary Δ

    postulate
      -- We assume that a class table doesn't have a class with name Obj
      Obj-∉-CT : ∀ {Δ} → ¬ (Obj ∈ Δ)
      -- We assume that a context is a set (i.e. there are no duplicate elements)      
      ∋-first : ∀ {A Δ x τ} {a : A} → ((x , a) ∷ Δ) ∋ x ∶ τ → a ≡ τ
      -- We assume a well-formed class table
      Δwf : CTOk Δ

    -- Properties related to operator _∋_∶_

    ∋-elim-≢ : ∀ {A Δ x y} {a b : A} → x ≢ y → ((y , b) ∷ Δ) ∋ x ∶ a → Δ ∋ x ∶ a
    ∋-elim-≢ p here = ⊥-elim (p refl)
    ∋-elim-≢ p (there hx) = hx

    ∋-∈ : ∀ {A Δ x} {τ : A} → Δ ∋ x ∶ τ → x ∈ (proj₁ (unzip Δ))
    ∋-∈ here = here refl
    ∋-∈ (there xi) = there (∋-∈ xi)

    ∋-interl : ∀ {E0 E ds Eds v t} → E0 ⊧ ds ∶ (proj₂ (unzip E)) → interl E ds Eds → E ∋ v ∶ t → (∃ λ e → Eds ∋ v ∶ e)
    ∋-interl {E0} {.(v , t) ∷ E} {x₁ ∷ ds} {.(v , x₁) ∷ Eds} {v} {t} tl (there ez) here = x₁ , here
    ∋-interl {E0} {.(_ , _) ∷ E} {x₁ ∷ ds} {.(_ , x₁) ∷ Eds} {v} {t} (there x₂ tl) (there ez) (there ni) = proj₁ (∋-interl tl ez ni) , there (proj₂ (∋-interl tl ez ni))

    -- Equalities

    ≡-∋ : ∀ {A Δ x} {a b : A} → Δ ∋ x ∶ a → Δ ∋ x ∶ b → a ≡ b
    ≡-∋ {Δ = (y , _) ∷ Δ} {x = x} ha hb with x ≟ y
    ... | yes refl rewrite ∋-first ha | ∋-first hb = refl
    ... | no ¬p = ≡-∋ (∋-elim-≢ ¬p ha) (∋-elim-≢ ¬p hb)

    ≡-fields : ∀ {c fs fs'} → fields c fs → fields c fs' → fs ≡ fs'
    ≡-fields obj obj = refl
    ≡-fields obj (other c b) with ∋-∈ c
    ... | obi = ⊥-elim (Obj-∉-CT obi)
    ≡-fields (other c a) obj with ∋-∈ c
    ... | obi = ⊥-elim (Obj-∉-CT obi)
    ≡-fields (other c₁ a) (other c₂ b) rewrite ≡-∋ c₁ c₂ | ≡-fields a b = refl

    ≡-method : ∀ {c m md md'} → method c m md → method c m md' → md ≡ md'
    ≡-method (this cd₁ md₁) (this cd₂ md₂) rewrite ≡-∋ cd₁ cd₂ | ≡-∋ md₁ md₂ = refl

    -- Properties related to _⊢_∶_ and _⊧_∶_

    ⊢-interl : ∀ {Δ₁ Δ₂ el Γ f e τ} → interl Δ₁ el Δ₂ → Γ ⊧ el ∶ proj₂ (unzip Δ₁) → Δ₁ ∋ f ∶ τ → Δ₂ ∋ f ∶ e → Γ ⊢ e ∶ τ
    ⊢-interl {f = f} (there {x} zp) (there t env) ht he with f ≟ x
    ... | yes refl rewrite ∋-first he | ∋-first ht = t
    ... | no ¬p = ⊢-interl zp env (∋-elim-≢ ¬p ht) (∋-elim-≢ ¬p he)

    ⊧-interl : ∀ {Δ₁ Δ₂ vl} → Δ₁ ⊧ vl ∶ (proj₂ (unzip Δ₂)) → (∃ λ zp → interl Δ₂ vl zp)
    ⊧-interl {Δ₂ = []} {[]} tl = [] , here
    ⊧-interl {Δ₁} {Δ₂ = (n , t) ∷ xl} {e ∷ vl} (there x tl) = (n , e) ∷ proj₁ (⊧-interl {Δ₁} {xl} tl) , there (proj₂ (⊧-interl tl))

    -- Properties about CT

    meth-lookup : ∀ {CD MD m ml} → All (MethodOk CD) (proj₂ (unzip ml)) → ml ∋ m ∶ MD → MethodOk CD MD
    meth-lookup (m ∷ ml) here = m
    meth-lookup (m ∷ ml) (there i) = meth-lookup ml i

    ok-class-meth : ∀ {CD MD m} → ClassOk CD → Class.meths CD ∋ m ∶ MD → MethodOk CD MD
    ok-class-meth (T-Class meths) m = meth-lookup meths m

    ok-ctable-class : ∀ {Δ CD c} → CTOk Δ → Δ ∋ c ∶ CD → ClassOk CD
    ok-ctable-class (cd ∷ ctok) here = cd
    ok-ctable-class (cd ∷ ctok) (there c) = ok-ctable-class ctok c

    ⊢-method : ∀ {C m MD} → method C m MD → Meth.params MD ⊢ Meth.body MD ∶ Meth.ret MD
    ⊢-method (this {_} {CD} cd md) with ok-class-meth (ok-ctable-class Δwf cd) md
    ... | T-Method tm = tm


  module Properties (Δ : CT) where

    open AuxiliaryLemmas Δ
    open Eval Δ
    open Typing Δ


    -- Substitution lemma

    subst-var : ∀ {Γ Γ₁ x el pe C} → Γ ∋ x ∶ C → Γ₁ ⊧ el ∶ proj₂ (unzip Γ) → interl Γ el pe → Γ₁ ⊢ subs (Var x) pe ∶ C
    subst-var {.[]} {Γ₁} {x} {.[]} {[]} {C} () here here
    subst-var {((y , _) ∷ xs)} {Γ₁} {x} {.(_ ∷ _)} {.(_ , _) ∷ pe} {C} v (there t env) (there zp) with x ≟ y
    ... | yes refl rewrite ∋-first v = t
    ... | no ¬p = subst-var (∋-elim-≢ ¬p v) env zp


    subst : ∀ {Γ Γ₁ e pe C el} → Γ₁ ⊢ e ∶ C → Γ ⊧ el ∶ proj₂ (unzip Γ₁) → interl Γ₁ el pe → Γ ⊢ (subs e pe) ∶ C
    subst-list : ∀ {Γ Γ₁ el pe Cl nl} → Γ₁ ⊧ el ∶ Cl → Γ ⊧ nl ∶ proj₂ (unzip Γ₁) → interl Γ₁ nl pe → Γ ⊧ (subs-list el pe) ∶ Cl

    subst (T-Var v) pt zp = subst-var v pt zp
    subst (T-Field e flds f) pt zp = T-Field (subst e pt zp) flds f
    subst (T-Invk e m mp) pt zp = T-Invk (subst e pt zp) m (subst-list mp pt zp)
    subst (T-New flds cp) pt zp = T-New flds (subst-list cp pt zp)

    subst-list here pt zp = here
    subst-list (there t tl) pt zp = there (subst t pt zp) (subst-list tl pt zp)

    -- Auxiliary definitions for Progress


    data Progress (e : Expr) : Set where
      Step : ∀ {e'}
          → e ⟶ e'
          → Progress e
      Done : Val e
          → Progress e

    data ProgressList (el : List Expr) : Set where
      Step : ∀ {el'}
          → el ↦ el'
          → ProgressList el
      Done : All Val el
          → ProgressList el    
    

    -- Progress proof

    progress : ∀ {e τ} → [] ⊢ e ∶ τ → Progress e
    progress-list : ∀ {el tl} → [] ⊧ el ∶ tl → ProgressList el

    progress (T-Var ()) -- this is not necessary anymore
    progress (T-Field tp fls bnd) with progress tp
    progress (T-Field tp fls bnd) | Step ev = Step (RC-Field ev)
    progress (T-Field (T-New flds fts) fls bnd) | Done ev rewrite ≡-fields flds fls =
      Step (R-Field fls (proj₂ (⊧-interl fts)) (proj₂ (∋-interl fts (proj₂ (⊧-interl fts)) bnd)))
    progress (T-Invk tp mt tpl) with progress tp
    progress (T-Invk tp mt tpl) | Step ev = Step (RC-InvkRecv ev)
    progress (T-Invk tp mt tpl) | Done ev with progress-list tpl
    progress (T-Invk tp mt tpl) | Done ev | Step evl = Step (RC-InvkArg evl) 
    progress (T-Invk (T-New flds fts) mt tpl) | Done ev | Done evl = Step (R-Invk mt (proj₂ (⊧-interl tpl)))
    progress (T-New fls tpl) with progress-list tpl
    progress (T-New fls tpl) | Step evl = Step (RC-NewArg evl)
    progress (T-New fls tpl) | Done evl = Done (V-New evl)

    progress-list here = Done []
    progress-list (there tp tpl) with progress tp
    ... | Step ev = Step (here ev)
    ... | Done ev with progress-list tpl
    ...   | Step evl = Step (there evl)
    ...   | Done evl = Done (ev ∷ evl)

    -- Preservation proof

    preservation : ∀ {e e' τ} → [] ⊢ e ∶ τ → e ⟶ e' → [] ⊢ e' ∶ τ
    preservation-list : ∀ {el el' τl} → [] ⊧ el ∶ τl → el ↦ el' → [] ⊧ el' ∶ τl

    preservation (T-Var x) () -- Not necessary anymore
    preservation (T-Field tp fls bnd) (RC-Field ev) = T-Field (preservation tp ev) fls bnd
    preservation (T-Field (T-New fs₁ tps) fs₂ bnd) (R-Field fs₃ zp bnde)
      rewrite ≡-fields fs₁ fs₂ | ≡-fields fs₂ fs₃ = ⊢-interl zp tps bnd bnde
    preservation (T-Invk tp tmt tpl) (RC-InvkRecv ev) = T-Invk (preservation tp ev) tmt tpl
    preservation (T-Invk tp tmt tpl) (RC-InvkArg evl) = T-Invk tp tmt (preservation-list tpl evl)
    preservation (T-Invk (T-New fls cp) tmt tpl) (R-Invk rmt zp) rewrite ≡-method rmt tmt = subst (⊢-method tmt) tpl zp
    preservation (T-New fls tpl) (RC-NewArg evl) = T-New fls (preservation-list tpl evl)

    preservation-list here () -- Not necessary anymore
    preservation-list (there tp tpl) (here ev) = there (preservation tp ev) tpl
    preservation-list (there tp tpl) (there evl) = there tp (preservation-list tpl evl)

  module Evaluation (Δ : CT) where

    open Eval Δ
    open Typing Δ
    open Properties Δ

    Fuel = ℕ

    infix 2 _↠_
    data _↠_ : Expr → Expr → Set where
      refl  : ∀ {e} → e ↠ e
      multi : ∀ {e e' e''} → e ⟶ e' → e' ↠ e'' → e ↠ e''

    data Finished (e : Expr) : Set where
      done       : Val e → Finished e
      out-of-gas : Finished e

    data Steps (e : Expr) : Set where
      steps : ∀ {e'} → e ↠ e' → Finished e' → Steps e

    eval : ∀ {e τ} → Fuel → [] ⊢ e ∶ τ → Steps e
    eval zero t = steps refl out-of-gas
    eval (suc fuel) t with progress t
    ... | Done vl = steps refl (done vl)
    ... | Step stp with eval fuel (preservation t stp)
    ...   | steps stp' fin = steps (multi stp stp') fin

