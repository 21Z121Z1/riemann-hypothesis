import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompTie
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def OrdTie (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f

def OrdTieQ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c, ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
      (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompTieA
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

theorem ramIdx_nonneg_of_isOver {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)} (h : IsOver (K := K) v la) :
    0 ≤ ramIdx v la := by
  have h' := h
  unfold IsOver at h'
  unfold ramIdx
  by_cases hne : {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v (algebraMap K Ω (a : K)) = n}.Nonempty
  · apply le_csInf hne
    rintro n ⟨a, ha, -, hv⟩
    have h0 := (h' a).2 ha
    rw [hv] at h0
    exact_mod_cast h0.le
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Int.csInf_empty]

theorem int_nonneg_of_ereal_eq {x e : ℤ} {w : EReal} (he : 0 ≤ e) (hw : 0 ≤ w)
    (h : (((x : ℤ) : ℝ) : EReal) = (((e : ℤ) : ℝ) : EReal) * w) : 0 ≤ x := by
  have h1 : (0 : EReal) ≤ (((e : ℤ) : ℝ) : EReal) * w := EReal.mul_nonneg (by exact_mod_cast he) hw
  rw [← h] at h1
  have h2 : (0 : ℝ) ≤ ((x : ℤ) : ℝ) := by exact_mod_cast h1
  exact_mod_cast h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vAtV_mem_valSet {cls cls' : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop}
    (hc : ∀ T io y, cls T io y → cls' T io y) {PY : Type}
    {lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) :
    vAtV y ∈ valSet Xo c cls' la := by
  unfold vAtV valSet
  refine ⟨⟨((y.1).1, ()), ?_⟩, rfl⟩
  obtain ⟨T, io, e, hO, y1, hcl, eta, -, hy⟩ := y.2
  refine ⟨T, io, e, hO, y1, hc T io y1 hcl, (), trivial, ?_⟩
  rw [hy]
  rfl

theorem vV_of_trivCls {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (h : trivCls Xo c T io y)
    (a : c.F) (ha : a ≠ 0) : vV T.V (io a) = 0 := by
  unfold trivCls at h
  unfold vV
  obtain ⟨u, hu⟩ := h a ha
  rw [← hu]
  unfold valV
  have hnm : (u : T.V) ∉ (IsDiscreteValuationRing.maximalIdeal T.V).asIdeal := by
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm u.isUnit
  have hu1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr u) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    first
      | exact le_antisymm (HeightOneSpectrum.intValuation_le_one _ _)
          (not_lt.mp fun hlt => hnm ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mp hlt))
      | exact (HeightOneSpectrum.intValuation_eq_one_iff_not_mem _ _).mpr hnm
      | exact le_antisymm (HeightOneSpectrum.intValuation_le_one _ _)
          (not_lt.mp fun hlt => hnm ((HeightOneSpectrum.intValuation_lt_one_iff_dvd _ _).mp hlt))
      | simp [HeightOneSpectrum.intValuation_def, Ideal.span_singleton_eq_top.mpr u.isUnit]
  rw [hu1]
  simp

theorem valC_add (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f g : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (f + g) Z = valC h a n f Z + valC h a n g Z := by
  simp only [valC, evC, evR]
  rw [evalAt_add, AddMonoidAlgebra.single_add]

theorem valC_zero (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Z : Comp Xo c) :
    valC h a n 0 Z = 0 := by
  simp only [valC, evC, evR]
  rw [evalAt_zero, AddMonoidAlgebra.single_zero]

theorem valC_smul_ct (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : c.F) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (t • f) Z = algebraMap c.F (AC Z) t * valC h a n f Z := by
  simp only [valC, evC, evR]
  rw [evalAt_smul, ← Algebra.smul_def, ← Algebra.smul_def, AddMonoidAlgebra.smul_single]

theorem evC_ne_zero_of_valC {h : GenFrEx Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} {Z : Comp Xo c}
    (hf : valC h a n f Z ≠ 0) : evC h Z f ≠ 0 := by
  intro h0
  apply hf
  unfold valC
  rw [h0, AddMonoidAlgebra.single_zero]

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def offZero {Comp : Type} (X : Comp → Data E r) : Submodule ℂ (FDSec X) where
  carrier := {P | ∀ k x, x ∉ (X k).dom → P k x = 0}
  zero_mem' _ _ _ := rfl
  add_mem' hP hQ k x hx := by simp [hP k x hx, hQ k x hx]
  smul_mem' a P hP k x hx := by simp [hP k x hx]

def holSub0 {Comp : Type} (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) : Submodule ℂ (FDSec X) :=
  holSub X la ⊓ offZero X

variable {Xo c} in
theorem rdU_mem_offZero {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (f : Rul Xo c) : rdU V f ∈ offZero V.X :=
  fun _ _ hx => dif_neg hx

variable {Xo c} in

def HolomorphicSectionsFinDim {σ : c.F →+* ℂ} (V : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional ℂ (holSub0 V.X (laU V a n))

def HolFD0 (σ : c.F →+* ℂ) : Prop := HolomorphicSectionsFinDim (U σ)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Core (D : D7) : Type 1 where
  Q : Par D
  U : ∀ j (σ : Q.c.F →+* ℂ), Unf (Q.Xo j) Q.c σ D.R.r
  V : ℕ → (Q.c.F →+* ℂ) → HSp D
  dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r
  mu : ∀ j σ, GA D (V j σ) → ℂ
  Kf : ∀ j σ, Subgroup (GA D (V j σ))
  pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)

variable {D : D7}

def latHat (V : HSp D) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ a : Af D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) ∧
    ∃ x ∈ V.L0, z = fun i => a ⊗ₜ V.frame.repr x i}

def IsLevelK (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

def xiR (D : D7) : ℝ := ‖D.host.φ₀ D.host.xi0‖

namespace Core

variable (T : Core D)

def σ₀ : T.Q.c.F →+* ℂ := T.Q.c.F.val.toRingHom

theorem good_σ₀ : GoodEmb T.Q.c T.σ₀ := rfl

abbrev R (j : ℕ) : Type := Rul (T.Q.Xo j) T.Q.c

abbrev cuspA (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule T.Q.c.F (T.R j) :=
  cusp (T.Q.Xo j) T.Q.c (T.U j) a n

abbrev X₀ (j : ℕ) : (T.U j T.σ₀).Comp → Data D.host.E D.R.r := (T.U j T.σ₀).X

def frI (_T : Core D) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := 1

abbrev PtM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def nrmM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) : ℝ := nrmOf la (y.1 f)

theorem nrmM_le_one_iff (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) :
    T.nrmM j la y f ≤ 1 ↔ 0 ≤ y.1 f := by
  unfold nrmM nrmOf
  have hy := y.2
  unfold valSet at hy
  obtain ⟨x, hx⟩ := hy
  unfold vAtV at hx
  obtain ⟨T1, io, e, -, y', -, eta, -, hxe⟩ := x.2
  rw [hxe] at hx
  unfold profI at hx
  have key : y.1 f = nval T1.V e (evI y' f) := by rw [← hx]
  unfold nval at key
  have hN : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    have h1 : Ideal.absNorm la.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact la.isPrime.ne_top
    exact_mod_cast (by omega : 1 < Ideal.absNorm la.asIdeal)
  rw [key]
  by_cases hz : evI y' f = 0
  · simp [hz]
  · simp only [hz, if_false, EReal.coe_ne_top, EReal.toReal_coe, EReal.coe_nonneg]
    constructor
    · intro h
      by_contra hneg
      exact absurd h (not_le.mpr (Real.one_lt_rpow hN (neg_pos.mpr (not_le.mp hneg))))
    · intro h
      exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (neg_nonpos.mpr h)

def phiAd (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) • adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f)

end Core

structure LawsM (T : Core D) : Prop where

  pins : T.Q.Pins

  half : (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal) ∧
    T.Q.l.Mb = ∏ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

  evalWD : ∀ j, InR D j → EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)

  unf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ)

  unTest : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k x,
    FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) ((T.U j σ).un k x)
  chiTriv : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
    ((T.U j σ).X k).χ (laU (T.U j σ) a n k) γ = 1

  dictU : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (T.V j σ) (T.dict j σ) (T.Kf j σ) th hr

  spaceW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j
  levelK : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsLevelK (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ)

  xiAbs : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((T.U j σ).X k).ξ0‖ = xiR D
  muUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuUnit (T.V j σ) (T.dict j σ) (T.mu j σ)
  muCont : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → Continuous (T.mu j σ)
  finVol : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → FinVol (T.V j σ)

  cuspFD : ∀ j, InR D j → CuspFD (T.Q.Xo j) T.Q.c (T.U j)

  supDef : ∀ j, InR D j → SupDef (T.Q.Xo j) T.Q.c (T.U j)

  cuspidalL2Subspace : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ)
  l2Def : ∀ j (hj : InR D j) σ (hσ : GoodEmb T.Q.c σ),
    L2DefiniteCuspForms (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) (cuspidalL2Subspace j hj σ hσ)

  unitIndep : ∀ j, InR D j → UnitIndep (T.Q.Xo j) T.Q.c
  ptNe : ∀ j, InR D j → IntFrNe (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)

structure LawsCore (T : Core D) : Prop extends LawsM T where

  cuspMul : ∀ j, InR D j → CuspMul (T.Q.Xo j) T.Q.c (T.U j)

  latZ : ∀ j, InR D j → FJ.LatZ (T.X₀ j) (WeightFamilies.rho D j)
  cuNe : ∀ j, InR D j → FJ.CuNeF (T.X₀ j) (WeightFamilies.rho D j)
  expo : ∀ j, InR D j → FJ.ExpoMatch (T.X₀ j) T.frI (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
section
noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem FDSec_eq (X : Comp → Data E r) : FDSec X = Formalism.L2.Pj.FDSec X := rfl

theorem isHolCusp_iff (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) :
    IsHolCusp X la P ↔ Formalism.L2.Pj.IsHolCusp X la P := by rfl

theorem supE_eq (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) :
    supE X la P = Formalism.L2.Pj.supE X la P := rfl

theorem supN_eq (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) :
    supN X la P = Formalism.L2.Pj.supN X la P := rfl

theorem holSub_eq (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : holSub X la = Formalism.L2.Pj.holSub X la := rfl

end Sections

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def Unf.ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

def Unf.toPj (U : Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

theorem Unf.toPj_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : (Unf.ofPj U).toPj = U := rfl

theorem Unf.ofPj_toPj (U : Unf Xo c σ r) : Unf.ofPj U.toPj = U := rfl

theorem rdU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (f : Formalism.L2.Pj.Rul Xo c) : rdU (Unf.ofPj U) f = Formalism.L2.Pj.rdU U f := rfl

theorem laU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    laU (Unf.ofPj U) a n k = Formalism.L2.Pj.laU U a n k := rfl

theorem isUnf_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : IsUnf (Unf.ofPj U) ↔ Formalism.L2.Pj.IsUnf U := by rfl

theorem goodEmb_iff (σ : c.F →+* ℂ) : GoodEmb c σ ↔ Formalism.L2.Pj.GoodEmb c σ := by rfl

theorem goodOf_eq (σ : c.F →+* ℂ) : goodOf c σ = Formalism.L2.Pj.goodOf c σ := rfl

theorem lieFac_eq (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : lieFac Dw x a = Formalism.L2.Pj.lieFac Dw x a := rfl

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)

theorem cusp_ofPj (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (fun σ => Unf.ofPj (U σ)) a n = Formalism.L2.Pj.cusp Xo c U a n := rfl

theorem cuspMul_ofPj : CuspMul Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspMul Xo c U := by rfl

theorem cuspFD_ofPj : CuspFD Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspFD Xo c U := by rfl

theorem supC_ofPj (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Formalism.L2.Pj.Rul Xo c) :
    supC Xo c (fun σ => Unf.ofPj (U σ)) x σ a n f = Formalism.L2.Pj.supC Xo c U x σ a n f := rfl

theorem supDef_ofPj : SupDef Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.SupDef Xo c U := by rfl

theorem regP_ofPj : regular₂ Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.regular₂ Xo c U := by rfl

end Unif

section Points

theorem isVal_iff {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : IsVal la v ↔ Formalism.L2.Pj.IsVal la v := by
  constructor
  · intro hv
    cases hv
    constructor <;> assumption
  · intro hv
    cases hv
    constructor <;> assumption

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) (cls : ∀ (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr), Formalism.L2.Pj.IntFr Xo c T ι → Prop)

theorem algCls_iff (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr) (y : Formalism.L2.Pj.IntFr Xo c T ι) :
    algCls Xo c T ι y ↔ Formalism.L2.Pj.algCls Xo c T ι y := by rfl

theorem valSet_eq (la : HeightOneSpectrum (𝓞 c.F)) : valSet Xo c cls la = Formalism.L2.Pj.valSet Xo c cls la := rfl

theorem allCls_iff (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr) (y : Formalism.L2.Pj.IntFr Xo c T ι) :
    trivialClassCondition Xo c T ι y ↔ Formalism.L2.Pj.trivialClassCondition Xo c T ι y := by rfl

theorem trivSet_eq : trivSet Xo c = Formalism.L2.Pj.trivSet Xo c := rfl

theorem noCommonZero_iff {n : ℕ} (ws : Fin n → Formalism.L2.Pj.Rul Xo c) :
    NoCommonZero Xo c ws ↔ Formalism.L2.Pj.NoCommonZero Xo c ws := by rfl

end Points

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {r : ℕ}

theorem perFr_eq (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x v τ i = Formalism.L2.Pj.perFr X x v τ i := rfl

theorem relab_eq (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) : relab c σ τ = Formalism.L2.Pj.relab c σ τ := rfl

end Frames

end Formalism.L2.PjFree
end
end

