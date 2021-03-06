{-# OPTIONS --cumulativity #-}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
mutual
  data Context : Set j where
    ∅ : Context
    _,_ : (ctx : Context) → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ctx , h) = Σ (ctxType ctx) (λ t → h t)

  data InCtx : Context → Set j where
    same : ∀{Γ T} → InCtx (Γ , T)
    next : ∀{Γ T} → InCtx Γ → InCtx (Γ , T)

  CtxAt : ∀{Γ} → InCtx Γ → Context
  CtxAt {(Γ , _)} same = Γ
  CtxAt {(_ , _)} (next icx) = CtxAt icx

  TypeAt : ∀{Γ} → (icx : InCtx Γ) → (ctxType Γ → Set i)
  TypeAt {(_ , T)} same (γ , _) = T γ
  TypeAt {.(_ , _)} (next icx) (γ , _) = TypeAt icx γ

  proj : ∀{Γ} → (icx : InCtx Γ) → (γ : ctxType Γ) → TypeAt icx γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

mutual
  data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Π₀ : {Γ : Context} → (A : Exp Γ (λ γ → Set₀))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₀))
      → Exp Γ (λ γ → Set₀)
    Π₀₁ : {Γ : Context} → (A : Exp Γ (λ γ → Set₀))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₀))
      → Exp Γ (λ γ → Set₁)
    Π₁ : {Γ : Context} → (A : Exp Γ (λ γ → Set₁))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₁))
      → Exp Γ (λ γ → Set₁)
    Π₂ : {Γ : Context} → (A : Exp Γ (λ γ → Set₂))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₂))
      → Exp Γ (λ γ → Set₂)
    𝓤₀ : {Γ : Context} → Exp Γ (λ γ → Set₁)
    𝓤₁ : {Γ : Context} → Exp Γ (λ γ → Set₂)
    𝓤₂ : {Γ : Context} → Exp Γ (λ γ → Set₃)
    Var : ∀{Γ} → (icx : InCtx Γ)
      → Exp Γ (λ γ → TypeAt icx γ)
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
        -- TODO: compare this definition of App with old

  -- unquote
-- TODO : should move γ arg to end
  unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Var icx) = proj icx γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₀₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₂ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set₀
  unq γ 𝓤₁ = Set₁
  unq γ 𝓤₂ = Set₂

idE : Exp ∅ (λ γ → (T : Set₀) → T → T)
idE = Lambda (Lambda (Var same)) -- λ T t . t

proofSame : unq tt idE ≡ (λ T t → t)
proofSame = refl

idE' : ∀{Γ} → Exp Γ (λ γ → (T : Set₀) → T → T)
idE' = Lambda (Lambda (Var same)) -- λ T t . t

idtype : ∀{Γ} → Exp Γ (λ γ → Set₁)
idtype = Π₁ 𝓤₀ (Π₀₁ (Var same) (Var (next same)))

freeVars : Exp (∅ , (λ γ → (T : Set₁) → T → T)) (λ γ → (T : Set₀) → T → T)
freeVars = App (App (Var same) idtype) idE'

-- Think: why are substitution and weakening hard/neccesary?

f1 : Exp ∅ (λ γ → (A B : Set₀) → (A → B) → A → B)
f1 = Lambda (Lambda (Lambda (Lambda (App (Var (next same)) (Var same)))))
-- λ A B f x . f x

------------------------------------------------------------------------
------------------------------------------------------------------------


TypeAt' : ∀{Γ} → (icx : InCtx Γ) → (ctxType (CtxAt icx) → Set i)
TypeAt' {(_ , T)} same = T
TypeAt' (next icx) = TypeAt' icx


mutual
  -- Substitution
  subΓ : ∀{Γ} → (icx : InCtx Γ) → Exp (CtxAt icx) (TypeAt' icx) → Context
  subΓ {(Γ , _)} same e = Γ
  subΓ {(_ , T)} (next icx) e = (subΓ icx e , λ γ → T (subγ icx e γ))
  -- subΓ {(_ , T)} (next icx) e = (subΓ icx e , λ γ → {!   !} )

  subγ : ∀{Γ} → (icx : InCtx Γ) → (e : Exp (CtxAt icx) (TypeAt' icx))
    → ctxType (subΓ icx e) → ctxType Γ
  subγ same e γ = (γ , unq γ e)
  subγ (next icx) e (γ , t) = (subγ icx e γ , t)

subT : ∀{Γ} → (icx : InCtx Γ) → (e : Exp (CtxAt icx) (TypeAt' icx))
  → (ctxType Γ → Set i) → (ctxType (subΓ icx e) → Set i)
subT icx e T = λ γ → T (subγ icx e γ)
  -- subT same e T γ =  T (γ , unq γ e)
  -- subT (next icx) e T = {!   !}

subExp : ∀{Γ T} → (icx : InCtx Γ) → (e : Exp (CtxAt icx) (TypeAt' icx))
  → Exp Γ T → Exp (subΓ icx e) (subT icx e T)
commute : ∀{Γ T} → ∀(icx) → (toSub : Exp (CtxAt {Γ} icx) (TypeAt' {Γ} icx))
  → (A : Exp Γ T)
  → _≡_ {_} -- {(γ : ctxType (subΓ {Γ} icx toSub)) → T (subγ icx toSub γ) }
      (λ γ → unq (subγ icx toSub γ) A) (λ γ → unq γ (subExp icx toSub A))

-- TODO: will need to prove that substitution commutes with unquoting
subExp icx toSub (Lambda e) = Lambda (subExp (next icx) toSub e)
subExp icx toSub (Π₀ {Γ} A B) = let x = subExp (next icx) toSub B
                            -- in Π₀ (subExp icx toSub A) x
                            in {!  subExp icx toSub A  !}
                            -- in Π₀ {subΓ icx toSub} {! subT icx toSub (λ γ → Set)  !} x
                              -- (subst (λ Γ → Exp (subΓ icx toSub , Γ) (λ γ → Set))
                                -- {! commute {_} {λ γ → Set₂} icx toSub A  !} x)
                            -- TODO: c-c c-n above!!!!!! (and look at c-c c-c)
subExp icx toSub (Π₀₁ A A₁) = {!   !}
subExp icx toSub (Π₁ A B) = {!   !}
subExp icx toSub (Π₂ A B) = {!   !}
subExp icx toSub 𝓤₀ = 𝓤₀
subExp icx toSub 𝓤₁ = 𝓤₁
subExp icx toSub 𝓤₂ = 𝓤₂
subExp icx toSub (Var icx₁) = {!   !} -- split on icx and icx₁, return Var or toSub.
subExp icx toSub (App {Γ} {A} {B} e₁ e₂) -- = {!   !}
  = let x = subExp icx toSub e₁
        y = subExp icx toSub e₂
    in {!   !}
    -- in App {subΓ icx toSub} {subT icx toSub A} {subT (next icx) toSub B}
      -- x {!   !}

-- TODO: can't prove this without function extentionality!!!!!!!!!!!!!!!
commute icx toSub (Lambda A) = let x = commute (next icx) toSub A in {!  (λ γ₂ → unq (subγ icx toSub (proj₁ γ₂) , proj₂ γ₂) A) !}
-- desired type is _≡ₐ_
-- x is _≡ₐₐ_
-- where a = (γ₁ : ctxType (subΓ icx toSub)) (x₁ : A₁ (subγ icx toSub γ₁))
--           → B (subγ icx toSub γ₁ , x₁)
-- aa = (γ₂ : Σ (ctxType (subΓ icx toSub)) (λ v → A₁ (subγ icx toSub v))) →
--           B (subγ icx toSub (proj₁ γ₂) , proj₂ γ₂)
commute icx toSub (Π₀ A A₁) = {!   !}
commute icx toSub (Π₀₁ A A₁) = {!   !}
commute icx toSub (Π₁ A A₁) = {!   !}
commute icx toSub (Π₂ A A₁) = {!   !}
commute icx toSub 𝓤₀ = refl
commute icx toSub 𝓤₁ = refl
commute icx toSub 𝓤₂ = refl
commute icx toSub (Var icx₁) = {!   !}
commute icx toSub (App A A₁) = {!   !}

data _↦_ : ∀{Γ T} → Exp Γ T → Exp Γ T → Set j where
  APP : {Γ : Context} → {A : ctxType Γ → Set i} → {B : (γ : ctxType Γ) → A γ → Set i} →
      (e e' : Exp Γ (λ γ → (a : A γ) → B γ a)) → e ↦ e'
      → (e₂ : Exp Γ A) → App e e₂ ↦ App e' e₂
