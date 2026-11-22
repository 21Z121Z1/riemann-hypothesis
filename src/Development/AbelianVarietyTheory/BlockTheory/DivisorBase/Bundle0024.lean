import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev OAf (D : D7) : Subring (EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def finR (V : HSp D) {r : ℕ} (hr : V.rank = r) : GA D V →* GL (Fin r) (EAf D) :=
  (Units.map (Matrix.reindexRingEquiv (EAf D) (finCongr hr)).toRingHom.toMonoidHom).comp (finE V)

def IsLatBasis (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) : Prop :=
  ∀ z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E, z ∈ latHat V ↔
    ∀ i, (Units.val (β⁻¹ : GL (Fin r) (EAf D))).mulVec
      (fun a => swapAE D (z (Fin.cast hr.symm a))) i ∈ OAf D

def IsLift (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (g : Formalism.L2.DIV.G0 Pg r) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ ∃ h : finR V hr κ ∈ Formalism.L2.DIV.St β, ∀ w : ↥Pg, Formalism.L2.DIV.redAt β w.1 ⟨finR V hr κ, h⟩ = g w

def chiDetG0 {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (Pg : Finset (Formalism.L2.DIV.Pl E)) (r : ℕ)
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ) : Formalism.L2.DIV.G0 Pg r →* Kˣ :=
  ∏ w : ↥Pg, (χ w).comp (Matrix.GeneralLinearGroup.det.comp
    (Pi.evalMonoidHom (fun w : ↥Pg => GL (Fin r) (Formalism.L2.DIV.kP w.1)) w))

def IsInvTame {K : Type} [Field K] (σ₀ : K →+* ℂ) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (μ : (AE D)ˣ →* Circle)
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ) : Prop :=
  ∀ (x : (AE D)ˣ) (u ub : (OAf D)ˣ), infPart D (x : AE D) = 1 →
    ((u : OAf D) : EAf D) = swapAE D (finPart D (x : AE D)) →
    ((ub : OAf D) : EAf D) = swapAE D (finPart D (cA D (x : AE D))) →
    ((μ x : Circle) : ℂ) =
      ∏ w : ↥Pg, (σ₀ ((χ w (Units.map (Formalism.L2.DIV.resS D.host.F w.1).toMonoidHom u) : Kˣ) : K))⁻¹ *
        σ₀ ((χ w (Units.map (Formalism.L2.DIV.resS D.host.F w.1).toMonoidHom ub) : Kˣ) : K)

def Induces {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (g : Formalism.L2.DIV.G0 Pg r) (γ : Dw.La →ₗ[𝓞 D.host.E] Dw.La) : Prop :=
  ∀ κ, IsLift V hr β Pg g κ →
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V 1,
        (finHom V κ).1.mulVec (finVec V (ι₀ a ∘ Fin.cast hr)) - finVec V (ι₀ (γ a) ∘ Fin.cast hr) = (l.M : ℕ) • w

def readAd (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (c : (T.U j σ).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : T.R j) (h : GA D (T.V j σ)) : ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (c (T.dict j σ h).1 * T.mu j σ h *
    rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2)

def levOf {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {G : Type} (γ : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La) (g : G) :
    (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La) :=
  (γ g, LinearMap.id)

def geoAct (T : Core D) (j : ℕ) {G : Type} [Group G] (γ : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) (g : G) :
    T.R j →ₗ[T.Q.c.F] T.R j :=
  actLev (Xo := T.Q.Xo j) T.Q.c (levOf γ) g

def IntegralAt (T : Core D) (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (f : T.R j) : Prop :=
  ∀ y : T.PtM j la, T.nrmM j la y f ≤ 1

structure LevelActionLaws (T : CoreJ D) (j : ℕ) (β : GL (Fin D.R.r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ)
    (γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) : Prop where

  act : ActLev (Xo := T.Q.Xo j) T.Q.c (levOf γ)

  cusp : ∀ a n, Dom a n → ∀ g, ∀ f ∈ T.toCore.cuspA j a n, geoAct T.toCore j γ g f ∈ T.toCore.cuspA j a n

  lift : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) g, ∃ κ, IsLift (T.V j σ) hr β Pg g κ

  read : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) (n : ℕ), Even n →
    ∃ c : (T.U j σ).Comp → ℂ, CUnit c ∧ ∀ a, Dom a n → ∀ g κ, IsLift (T.V j σ) hr β Pg g κ →
      ∀ f ∈ T.toCore.cuspA j a n, ∀ h : GA D (T.V j σ),
        readAd T.toCore j σ c a (geoAct T.toCore j γ g f) h =
          σ ((chiDetG0 Pg D.R.r χ g : (T.Q.c.F)ˣ) : T.Q.c.F) * readAd T.toCore j σ c a f (h * κ)

  integral : ∀ a n, Dom a n → ∀ g, ∀ f ∈ T.toCore.cuspA j a n, ∀ la,
    IntegralAt T.toCore j la f → IntegralAt T.toCore j la (geoAct T.toCore j γ g f)

def GeoLevelAction : Prop :=
  ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j →
    ∀ (hr : (D.sp.W j).rank = D.R.r) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)),
      (∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal) →
    ∀ β : GL (Fin D.R.r) (EAf D), IsLatBasis (D.sp.W j) hr β →
    ∀ χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ,
      IsInvTame T.toCore.σ₀ Pg (T.chiW j T.toCore.σ₀) χ →
      (∀ g, ∃ γ₀, Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g γ₀) ∧
      ∀ γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La,
        (∀ g, Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g (γ g)) → LevelActionLaws T j β Pg χ γ

theorem chiDetG0_apply {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (Pg : Finset (Formalism.L2.DIV.Pl E)) (r : ℕ)
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ) (g : Formalism.L2.DIV.G0 Pg r) :
    chiDetG0 Pg r χ g = ∏ w : ↥Pg, χ w (Matrix.GeneralLinearGroup.det (g w)) := by
  simp only [chiDetG0, MonoidHom.finset_prod_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]

theorem isLift_one (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) : IsLift V hr β Pg 1 1 := by

  have h1 : finR V hr 1 ∈ Formalism.L2.DIV.St β := by
    rw [map_one]
    exact Subgroup.one_mem _
  refine ⟨Subgroup.one_mem _, h1, fun w => ?_⟩
  have e : (⟨finR V hr 1, h1⟩ : Formalism.L2.DIV.St β) = 1 := Subtype.ext (map_one _)
  rw [e, map_one]
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Side (D : D7) (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ x : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E x)) =
    D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E x))

abbrev Emb (D : D7) : Type := {σ : D.what₂.LL →+* ℂ // Side D σ}

def SitsAt (D : D7) (σ : D.what₂.LL →+* ℂ) (τ τ' : D.what₂.Tau) : Prop :=
  ∃ t : D.host.E →+* D.what₂.LL, D.what₂.embLL.comp t = tauE D τ ∧ σ.comp t = tauE D τ'

def IsConjPar (D : D7) (j : ℕ) (σ : D.what₂.LL →+* ℂ) (S : D.what₂.Tau → SPar) : Prop :=
  ∀ τ', ∃ τ, SitsAt D σ τ τ' ∧ S τ' = parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)) τ

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def IsCover (V : HSp D) {G0 : Type} [Group G0] (Lift : G0 → GA D V → Prop) : Prop :=
  (∀ κ, κ ∈ levSet V 1 ↔ ∃ g, Lift g κ) ∧ (∀ g, ∃ κ, Lift g κ) ∧
    (∀ g g' κ, Lift g κ → Lift g' κ → g = g') ∧
    (∀ g g' κ κ', Lift g κ → Lift g' κ' → Lift (g * g') (κ * κ')) ∧
    ∀ κ, Lift 1 κ ↔ κ ∈ levSet V (D.host.g 0 * D.host.g 1)

abbrev MultK (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) : Submodule ℂ (MMap M) :=
  Mult θ M (levSet V (D.host.g 0 * D.host.g 1)) (fun _ => 1)

def UnifCl (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] {G0 : Type} [Group G0]
    (Lift : G0 → GA D V → Prop) (ρ : G0 →* (WL →ₗ[D.what₂.LL] WL)) (χ : G0 →* D.what₂.LLˣ) (σ : D.what₂.LL →+* ℂ)
    (J : WL →ₛₗ[σ] MMap M) : Prop :=
  (∀ (n : ℕ) (b : Fin n → WL), LinearIndependent D.what₂.LL b → LinearIndependent ℂ (fun i => J (b i))) ∧
    Submodule.span ℂ (Set.range J) = MultK θ M ∧
    ∀ g κ, Lift g κ → ∀ (x : WL) (v : M.Vec) (h : GA D V),
      J (ρ g x) v h = σ ((χ g : D.what₂.LLˣ) : D.what₂.LL) * J x v (h * κ)

def IsAnSide (j : ℕ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : Emb D → HSp D)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ, DSModel (V σ) (S σ)) {G0 : Type} [Group G0]
    (Lift : ∀ σ, G0 → GA D (V σ) → Prop) {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, AddCommGroup (W σ)]
    [∀ σ, Module ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ)) : Prop :=
  InR D j ∧ IsInfFam θ ∧ ∀ σ : Emb D, V σ = D.sp.W j ∧ IsConjPar D j σ.1 (S σ) ∧ IsCover (V σ) (Lift σ) ∧
    Function.Injective (ev σ) ∧ LinearMap.range (ev σ) = MultK θ (M σ)

def UnifEvery (j : ℕ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : Emb D → HSp D)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ, DSModel (V σ) (S σ)) {G0 : Type} [Group G0]
    (Lift : ∀ σ, G0 → GA D (V σ) → Prop) {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ))
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module Ks WL] [IsScalarTower Ks D.what₂.LL WL]
    (A : Formalism.IndefR.Arith.FormsL D.what₂.LL Ks WL W G0) : Prop :=
  IsAnSide j θ V S M Lift ev ∧ ∀ σ : Emb D, UnifCl θ (M σ) (Lift σ) A.ρ A.chi σ.1 ((ev σ).comp (A.j σ.1))

def IsKappa (j : ℕ) (e : D.what₂.Tau → ℤ) (w : WeightFamilies.Wt D j) : Prop :=
  (∀ τ (i : Fin D.R.m), i.1 + 1 = j → (e τ : ℚ) = (D.hc τ).e i) ∧ w.n = D.R.nV ∧
    (∀ τ i, (w.aP τ i : ℤ) + ((w.n / 2 : ℕ) : ℤ) =
      Formalism.L2.NTheta.kapW (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inl i) + e τ) ∧
    ∀ τ c, -(w.aM τ (Fin.rev c) : ℤ) - ((w.n / 2 : ℕ) : ℤ) =
      Formalism.L2.NTheta.kapW (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inr c) + e τ

def IsLowVec {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (v : M.Vec) : Prop :=
  ∀ τ, (v τ : M.H τ) ≠ 0 ∧ ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    M.rep τ g (v τ) ∈ Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ)

variable (T : CoreJ D) (j : ℕ)

abbrev GLev : Type := LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def geoAct (γ : GLev T j) : T.R j →ₗ[T.Q.c.F] T.R j :=
  actLev (Xo := T.Q.Xo j) T.Q.c (fun γ' : GLev T j => (liftLa γ', LinearMap.id)) γ

def Induces (V : HSp D) (γ : GLev T j) (κ : GA D V) : Prop :=
  κ ∈ levSet V 1 ∧ ∃ hr : V.rank = D.R.r, ∀ a : (T.Q.Dw j).La,
    (finHom V κ).1.mulVec (finVec V (T.iota j a ∘ Fin.cast hr)) - finVec V (T.iota j (liftLa γ a) ∘ Fin.cast hr) ∈
      AddSubgroup.closure {u | ∃ b ∈ T.Q.l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z}

abbrev Cu (w : WeightFamilies.Wt D j) : Type := T.cuspA j (wtA w) w.n

def rdK (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) (c : (T.U j s).Comp → ℂ) : T.R j →ₛₗ[s] (GA D (T.V j s) → ℂ) :=
  ((lieFac (T.Q.Dw j) (xiR D) (wtA w) : ℂ) •
    adel (T.V j s) (T.dict j s) (muPin (T.V j s) (T.dict j s) (T.mu j s) c)).comp (rdU (T.U j s))

variable [Algebra T.Q.c.F D.what₂.LL]

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

def rdL (w : WeightFamilies.Wt D j) (σ : D.what₂.LL →+* ℂ) (c : (T.U j (res T σ)).Comp → ℂ) :
    D.what₂.LL ⊗[T.Q.c.F] Cu T j w →ₛₗ[σ] (GA D (T.V j (res T σ)) → ℂ) :=
  extJ σ ((rdK T j w (res T σ) c).comp (T.cuspA j (wtA w) w.n).subtype)

def IsConjChar (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (e : D.what₂.Tau → ℤ)
    (χ : GLev T j →* D.what₂.LLˣ) (σ : D.what₂.LL →+* ℂ) : Prop :=
  (∀ τ τ', SitsAt D σ τ τ' → ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D (T.V j (res T σ)) τ'),
    T.mu j (res T σ) (atTau θ (T.V j (res T σ)) τ' h) = h.det ^ (-e τ)) ∧
  ∀ γ κ, Induces T j (T.V j (res T σ)) γ κ →
    T.mu j (res T σ) κ = (σ ((χ γ : D.what₂.LLˣ) : D.what₂.LL))⁻¹

def HidaSetting (w : WeightFamilies.Wt D j) (e : D.what₂.Tau → ℤ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (χ : GLev T j →* D.what₂.LLˣ) (S : Emb D → D.what₂.Tau → SPar) : Prop :=
  LawsJ T ∧ BaseEmbeddingInclusion T.Q.c.F D.what₂.embLL ∧ InR D j ∧ IsKappa j e w ∧ IsInfFam θ ∧
    ∀ σ : Emb D, IsConjChar T j θ e χ σ.1 ∧ IsConjPar D j σ.1 (S σ)

def FrameEquiv (w : WeightFamilies.Wt D j) (χ : GLev T j →* D.what₂.LLˣ) (σ : D.what₂.LL →+* ℂ)
    (c : (T.U j (res T σ)).Comp → ℂ) : Prop :=
  ∀ γ κ, Induces T j (T.V j (res T σ)) γ κ → ∀ (f : Cu T j w) (h : GA D (T.V j (res T σ))),
    rdK T j w (res T σ) c (geoAct T j γ f.1) h =
      σ ((χ γ : D.what₂.LLˣ) : D.what₂.LL) * rdK T j w (res T σ) c f.1 (h * κ)

def RowGeo : Prop :=
  ∀ (D : D7) (T : CoreJ D) (j : ℕ) [Algebra T.Q.c.F D.what₂.LL] (w : WeightFamilies.Wt D j) (e : D.what₂.Tau → ℤ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (χ : GLev T j →* D.what₂.LLˣ)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ : Emb D, DSModel (T.V j (res T σ.1)) (S σ)),
    HidaSetting T j w e θ χ S →
    ∃ ρC : GLev T j →* (Cu T j w →ₗ[T.Q.c.F] Cu T j w),
      (∀ γ f, (ρC γ f).1 = geoAct T j γ f.1) ∧
      (∀ γ (f : Cu T j w), (∀ la y, T.nrmM j la y f.1 ≤ 1) → ∀ la y, T.nrmM j la y (ρC γ f).1 ≤ 1) ∧
      ∀ σ : Emb D, IsCover (T.V j (res T σ.1)) (Induces T j (T.V j (res T σ.1))) ∧
        ∃ (c : (T.U j (res T σ.1)).Comp → ℂ) (v : (M σ).Vec)
          (J : D.what₂.LL ⊗[T.Q.c.F] Cu T j w →ₛₗ[σ.1] MMap (M σ)),
          CUnit c ∧ IsLowVec (M σ) v ∧ (∀ x, J x v = rdL T j w σ.1 c x) ∧
          UnifCl θ (M σ) (Induces T j (T.V j (res T σ.1))) (rhoOf D.what₂.LL ρC) χ σ.1 J

def Tied (w : WeightFamilies.Wt D j) (χ : GLev T j →* D.what₂.LLˣ) {S : Emb D → D.what₂.Tau → SPar}
    (M : ∀ σ : Emb D, DSModel (T.V j (res T σ.1)) (S σ)) {G0 : Type} [Group G0]
    {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ))
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module Ks WL] [IsScalarTower Ks D.what₂.LL WL]
    (A : Formalism.IndefR.Arith.FormsL D.what₂.LL Ks WL W G0) (eW : WL ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[T.Q.c.F] Cu T j w)
    (ℓ : G0 ≃* GLev T j) : Prop :=
  (∀ g (f f' : Cu T j w), f'.1 = geoAct T j (ℓ g) f.1 → eW (A.ρ g (eW.symm (1 ⊗ₜ f))) = 1 ⊗ₜ f') ∧
    (∀ g, A.chi g = χ (ℓ g)) ∧
    ∀ σ : Emb D,
      (∃ v : (M σ).Vec, IsLowVec (M σ) v ∧
        ∀ x, ev σ (A.j σ.1 x) v = rdL T j w σ.1 (T.cE j (res T σ.1)) (eW x)) ∧
      ((∃ c, CUnit c ∧ FrameEquiv T j w χ σ.1 c) → FrameEquiv T j w χ σ.1 (T.cE j (res T σ.1)))

def RowForms : Prop :=
  ∀ (D : D7) (T : CoreJ D) (j : ℕ) [Algebra T.Q.c.F D.what₂.LL] (w : WeightFamilies.Wt D j) (e : D.what₂.Tau → ℤ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (χ : GLev T j →* D.what₂.LLˣ)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ : Emb D, DSModel (T.V j (res T σ.1)) (S σ))
    (G0 : Type) [Group G0] (W : (D.what₂.LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ))
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (WL : Type) [AddCommGroup WL] [Module D.what₂.LL WL] [Module Ks WL] [IsScalarTower Ks D.what₂.LL WL]
    (A : Formalism.IndefR.Arith.FormsL D.what₂.LL Ks WL W G0) (eW : WL ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[T.Q.c.F] Cu T j w)
    (ℓ : G0 ≃* GLev T j),
    HidaSetting T j w e θ χ S → (∀ σ, Function.Injective (ev σ) ∧ LinearMap.range (ev σ) = MultK θ (M σ)) →
    Tied T j w χ M ev A eW ℓ →
    UnifEvery j θ (fun σ => T.V j (res T σ.1)) S M (fun σ g => Induces T j (T.V j (res T σ.1)) (ℓ g)) ev A

def Row : Prop := RowGeo ∧ RowForms

example (D : D7) : Side D D.what₂.embLL := fun _ => rfl

example (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) (f : T.R j) :
    rdK T j w s (T.cE j s) f = T.phiJ j s (wtA w) f := rfl

example (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) (h : IsLevelK V N Kf) : (Kf : Set (GA D V)) = levSet V N :=
  Set.ext h

end GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fam (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ

def comps (θ : InfFam D) {m n : ℕ} (w : Mx D m n) : Fam D m n := fun τ => compAt θ τ w

def realOf (θ : InfFam D) {m n : ℕ} (z : Fam D m n) : Mx D m n := ∑ τ, lineAt θ τ (z τ) 1

def ratFam {m n : ℕ} (γ : Matrix (Fin m) (Fin n) D.host.E) : Fam D m n := fun τ => γ.map (tauE D τ)

section Forms

variable (S T : HSp D)

def hAt (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  Matrix.trace ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x)

def efR (x y : Fam D T.rank S.rank) : ℝ :=
  -∑ τ, 2 * (tauE D τ D.host.xi0 * hAt S T τ (x τ) (y τ)).re

def cxJ (s : Fam D T.rank T.rank) (x : Fam D T.rank S.rank) : Fam D T.rank S.rank :=
  fun τ => cplxO 1 (s τ) (x τ)

def hermH (s : Fam D T.rank T.rank) (x y : Fam D T.rank S.rank) : ℂ :=
  (efR S T (cxJ S T s x) y : ℂ) + Complex.I * (efR S T x y : ℂ)

def hQ (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  Matrix.trace (S.gram⁻¹ * yᴴ * T.gram * x)

def qExp (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℚ :=
  Algebra.trace ℚ D.host.E (hQ S T x x) / (2 * (Ideal.absNorm D.host.ccK : ℚ))

def coordPt (s : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank) (BT : Fam D T.rank T.rank)
    (c : FVar D T.rank S.rank → ℂ) : Fam D T.rank S.rank := fun τ =>
  ((2 / fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
    ((((c (τ, i, j)).re : ℝ) : ℂ) • unitMap (BS τ) (BT τ) i j +
      (((c (τ, i, j)).im : ℝ) : ℂ) • cplxO 1 (s τ) (unitMap (BS τ) (BT τ) i j))

end Forms

section Moved

variable (θ : InfFam D) (S T : HSp D)

def movS (sT : Fam D T.rank T.rank) (g : GA D T) : Fam D T.rank T.rank :=
  fun τ => compAt θ τ (mt T g) * sT τ * compAt θ τ (mt T g⁻¹)

def movB (BT : Fam D T.rank T.rank) (g : GA D T) : Fam D T.rank T.rank :=
  fun τ => compAt θ τ (mt T g) * BT τ

def latG (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank) (g : GA D T) :
    Set (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
  {γ | ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True),
    (ratW T S γ).map (finPart D) = (actO S T 1 g u).map (finPart D)}

def frameFn (sT : Fam D T.rank T.rank) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ)
    (g : GA D T) (z : Fam D T.rank S.rank) : ℂ :=
  Complex.exp (Real.pi * hermH S T (movS θ T sT g) z z / 2) * om (1, g) f (realOf θ z)

end Moved

section Canon

variable (S T : HSp D) (s : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank) (BT : Fam D T.rank T.rank)
  (Γ : Set (Matrix (Fin T.rank) (Fin S.rank) D.host.E))

def IsCanon (G : Fam D T.rank S.rank → ℂ) : Prop :=
  Differentiable ℂ (fun c => G (coordPt S T s BS BT c)) ∧
    ∀ γ ∈ Γ, ∃ m : ℤ, qExp S T γ = m ∧ ∀ z, G (z + ratFam γ) = (-1) ^ m *
      Complex.exp (Real.pi * hermH S T s z (ratFam γ) + Real.pi * hermH S T s (ratFam γ) (ratFam γ) / 2) * G z

def coordLat : AddSubgroup (FVar D T.rank S.rank → ℂ) :=
  AddSubgroup.closure {c | ∃ γ ∈ Γ, coordPt S T s BS BT c = ratFam γ}

def MeanSq (G : Fam D T.rank S.rank → ℂ) (m : ℝ≥0∞) : Prop :=
  AllSome (fun Fd : Set (FVar D T.rank S.rank → ℂ) => IsAddFundamentalDomain (coordLat S T s BS BT Γ) Fd volume)
    fun Fd => volume Fd ≠ 0 ∧ volume Fd ≠ ⊤ ∧
      ∫⁻ c in Fd, ‖G (coordPt S T s BS BT c)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(Real.pi *
          (hermH S T s (coordPt S T s BS BT c) (coordPt S T s BS BT c)).re))) = m * volume Fd

end Canon

section Chars

def UnramInert (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (∀ e, IsSplitIdem D e → e * (x : AE D) = e) → χ x = 1

def IsSplitDet (T : HSp D) (k : GA D T) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ ∀ v ε, IsPlaceIdem D v ε →
    (∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε ∧
      e * (x : AE D) = e * (mt T k).det ∧ cA D e * (x : AE D) = cA D e) ∨
    ((¬ ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧
      algebraMap (AF D.host.F) (AE D) ε * (x : AE D) = algebraMap (AF D.host.F) (AE D) ε)

def detPos {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  (k * ((1 / 2 : ℂ) • (1 + s)) + (1 / 2 : ℂ) • (1 - s)).det

def detNeg {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ := detPos (-s) k

def vacChar (θ : InfFam D) (T : HSp D) (sT : Fam D T.rank T.rank) (n : ℕ) (a : D.what₂.Tau → ℤ) (k : GA D T) : ℂ :=
  ∏ τ, detPos (sT τ) (compAt θ τ (mt T k)) ^ (a τ + ((n / 2 : ℕ) : ℤ)) *
    detNeg (sT τ) (compAt θ τ (mt T k)) ^ (a τ - ((n / 2 : ℕ) : ℤ))

end Chars

def FrameLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (sT : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank)
    (BT : Fam D T.rank T.rank) (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank) (f : WO S T → ℂ) : Prop :=

  (∀ g, IsCanon S T (movS θ T sT g) BS (movB θ T BT g) (latG S T ΛS ΛT g) (frameFn θ S T sT om f g) ∧
    (∀ G, IsCanon S T (movS θ T sT g) BS (movB θ T BT g) (latG S T ΛS ΛT g) G →
      ∃ c : ℂ, G = c • frameFn θ S T sT om f g) ∧
    MeanSq S T (movS θ T sT g) BS (movB θ T BT g) (latG S T ΛS ΛT g) (frameFn θ S T sT om f g) 1) ∧

  (∀ g (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
    polyDeriv P (fun l => Pi.single l (1 : ℂ))
      (fun c => frameFn θ S T sT om f g (coordPt S T (movS θ T sT g) BS (movB θ T BT g) c)) 0 =
      thetaKO om 1 g (pureTensorO ψ θ S T (fun _ => 1) sT BS BT f P)) ∧

  (∀ γ ∈ GQ T, ∀ g z, frameFn θ S T sT om f (γ * g) (fun τ => compAt θ τ (mt T γ) * z τ) =
    frameFn θ S T sT om f g z) ∧

  (∀ k ∈ GfC T, IsMov (fmt T k) ΛT ΛT → AllSome (IsDetRoot T k) fun x =>
    ∀ g, frameFn θ S T sT om f (g * k) = ((χS x : Circle) : ℂ) • frameFn θ S T sT om f g) ∧

  (UnramInert χS → ∀ k ∈ GfC T, IsMov (fmt T k) ΛT ΛT → AllSome (IsSplitDet T k) fun x =>
    ∀ g, frameFn θ S T sT om f (g * k) = ((χS x : Circle) : ℂ) • frameFn θ S T sT om f g) ∧

  AllSome (fun a : D.what₂.Tau → ℤ => ∀ τ, HasInfExp D χS τ (a τ)) fun a =>
    ∀ k ∈ GinfC T, (∀ τ, compAt θ τ (mt T k) * sT τ = sT τ * compAt θ τ (mt T k)) →
      ∀ g, frameFn θ S T sT om f (g * k) = vacChar θ T sT S.rank a k • frameFn θ S T sT om f g

def AdelicFrame (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (sT : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank)
    (BT : Fam D T.rank T.rank) (pT : D.what₂.Tau → ℕ) (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank)
    (f : WO S T → ℂ),
    Even S.rank → Odd T.rank → (∀ τ, (gramAt D S τ).PosDef) →
    (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) →
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsWeilDatumO ψ S T χS χT om →
    IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f →
    FrameLaws ψ θ S T χS om sT BS BT ΛS ΛT f

def wZero (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

def IsHomology (T : HSp D) (L : Lt D.host.E T.rank) (g : GA D T) (H : Lt D.host.E T.rank) : Prop :=
  ∃ Λ : Lt D.host.E T.rank, IsAA Λ L ∧ ∀ v, v ∈ H ↔ ∃ u ∈ hatV Λ, toAf v = fmt T g *ᵥ u

def ClassicalFrame (D : D7) : Prop :=
  ∀ (S T : HSp D) (C : Ctx S T) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (L : Lt D.host.E T.rank) (f : WO S T → ℂ),
    Odd T.rank → C.IsB B → IsSelfDualC T L → IsWeilDatumO C.ψ S T χS χT om →
    IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (GlobalTheory.SW.stdL D.host.E S.rank) L f →
    ∀ g, AllSome (IsHomology T L g) fun H =>
      (∀ γ, γ ∈ latG S T (GlobalTheory.SW.stdL D.host.E S.rank) L g ↔ ∀ k, (fun a => γ a k) ∈ H) ∧
      AllSome (IsVac C.X C.bas (wZero D) (tens (GlobalTheory.SW.stdL D.host.E S.rank) H)) fun φ =>
        ∃ (c : ℂ) (m : ℝ), ‖c‖ ^ 2 * m = 1 ∧
          MeanSq S T (movS C.θ T (C.sB B) g) (fun _ => 1) (C.mvB g B) (latG S T (GlobalTheory.SW.stdL D.host.E S.rank) L g)
            (fun z => thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (realOf C.θ z)))
            (ENNReal.ofReal m) ∧
          (∀ z, frameFn C.θ S T (C.sB B) om f g z =
            c * thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (realOf C.θ z))) ∧
          ∀ Q, thetaKO om 1 g (C.fvec B f Q) = c * thP C.X C.hr C.bas C.idx φ (C.toH Q) (C.xB (C.mvB g B))

def VacuumFrame : Prop := ∀ D : D7, AdelicFrame D ∧ ClassicalFrame D

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

end
end

