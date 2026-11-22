import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetUnipotentOnBesselModels
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TypeAsm.CovTrans

open Formalism.L2.SG.LocWSOf

section Gen

variable {n m : ℕ} {ε : Fin n → Bool}

theorem conj_cancel (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (h : Q * Qi = 1)
    (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  calc Q * (Qi * A * Q) * Qi = (Q * Qi) * A * (Q * Qi) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem inUJ_conj (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (H : Matrix (Fin m) (Fin m) ℂ)
    (hQ : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (x : Matrix (Fin m) (Fin m) ℂ) (hx : xᴴ * H * x = H) :
    Formalism.REAL.inUJ ε (Q * x * Qi) := by
  unfold Formalism.REAL.inUJ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc Qiᴴ * (xᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * x * Qi) = Qiᴴ * (xᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * x) * Qi := by
        simp only [Matrix.mul_assoc]
    _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [hH, hx, ← hH]
    _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hQ]; simp

theorem inv_mul_of_inUJ (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) :
    Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = 1 := by
  calc Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε * (Mᴴ * Formalism.REAL.Jm ε * M) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h]; exact Formalism.REAL.Jm_mul_self ε

def mkUJ (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε, mul_eq_one_comm.1 (inv_mul_of_inUJ M h), inv_mul_of_inUJ M h⟩, h⟩

def mkUJ' (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε M then mkUJ M h else 1

theorem mkUJ'_val (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) :
    Formalism.MainNotions.S.uMat (mkUJ' ε M) = M := by
  rw [mkUJ', dif_pos h]; rfl

theorem mkUJ'_coe (γ : Formalism.REAL.UJ ε) :
    mkUJ' ε (((γ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = γ := by
  apply Subtype.ext; apply Units.ext
  exact mkUJ'_val _ γ.2

end Gen

section Tr

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

theorem trI_of (x : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trI C x τ) = C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ :=
  rfl

theorem vOf_pl (v : InfinitePlace X.B.I.F) : vOf X (X.pl v) = v := X.pl.symm_apply_apply v

theorem trI_mul (a b : X.B.I.Ginf) : trI C (a * b) = GlobalTheory.DegVol.mulP (trI C a) (trI C b) := by
  funext τ
  apply Matrix.of.injective
  show Matrix.of (trI C (a * b) τ) = Matrix.of (trI C a τ) * Matrix.of (trI C b τ)
  rw [trI_of, trI_of, trI_of]
  rw [show Formalism.MainNotions.S.uMat ((a * b) (vOf X τ)) = Formalism.MainNotions.S.uMat (a (vOf X τ)) * Formalism.MainNotions.S.uMat (b (vOf X τ)) from rfl]
  generalize Formalism.MainNotions.S.uMat (a (vOf X τ)) = A
  generalize Formalism.MainNotions.S.uMat (b (vOf X τ)) = B
  have h := (C.isT τ).2.1
  calc C.Qi τ * (A * B) * C.Q τ = C.Qi τ * A * (C.Q τ * C.Qi τ) * B * C.Q τ := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) := by simp only [Matrix.mul_assoc]

theorem trI_inj : Function.Injective (trI C) := by
  intro a b h
  funext v
  have e := congrArg Matrix.of (congrFun h (X.pl v))
  rw [trI_of, trI_of] at e
  have e2 : C.Q (X.pl v) * (C.Qi (X.pl v) * Formalism.MainNotions.S.uMat (a (vOf X (X.pl v))) * C.Q (X.pl v)) * C.Qi (X.pl v) =
      C.Q (X.pl v) * (C.Qi (X.pl v) * Formalism.MainNotions.S.uMat (b (vOf X (X.pl v))) * C.Q (X.pl v)) * C.Qi (X.pl v) := by rw [e]
  rw [conj_cancel _ _ (C.isT _).2.1, conj_cancel _ _ (C.isT _).2.1, vOf_pl] at e2
  exact Subtype.ext (Units.ext e2)

end Tr

section Back

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

def back (x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : X.B.I.Ginf :=
  fun v => mkUJ' (X.B.I.ε v) (C.Q (X.pl v) * Matrix.of (x (X.pl v)) * C.Qi (X.pl v))

def Sg : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  {x | ∀ τ, Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * Matrix.of (x τ) * C.Qi τ)}

theorem back_trI (a : X.B.I.Ginf) : back C (trI C a) = a := by
  funext v
  unfold back
  rw [trI_of, conj_cancel _ _ (C.isT _).2.1, vOf_pl]
  exact mkUJ'_coe _

theorem trI_back {x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS} (hx : x ∈ Sg C) : trI C (back C x) = x := by
  funext τ
  apply Matrix.of.injective
  rw [trI_of]
  unfold back
  have h := hx τ
  simp only [vOf, Equiv.apply_symm_apply] at h ⊢
  rw [mkUJ'_val _ h]
  calc C.Qi τ * (C.Q τ * Matrix.of (x τ) * C.Qi τ) * C.Q τ = (C.Qi τ * C.Q τ) * Matrix.of (x τ) * (C.Qi τ * C.Q τ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of (x τ) := by rw [(C.isT τ).1, Matrix.one_mul, Matrix.mul_one]

theorem range_trI : Set.range (trI C) = Sg C := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩ τ
    rw [trI_of]
    rw [conj_cancel _ _ (C.isT _).2.1]
    exact (a (vOf X τ)).2
  · intro hx
    exact ⟨back C x, trI_back C hx⟩

theorem cont_uMat {n : ℕ} {ε : Fin n → Bool} : Continuous (fun γ : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat γ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem measurable_trI : Measurable (trI C) := by
  refine measurable_pi_lambda _ (fun τ => ?_)
  have hc : Continuous (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * Formalism.MainNotions.S.uMat γ * C.Q τ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (continuous_const.matrix_mul cont_uMat).matrix_mul continuous_const
  exact hc.measurable.comp (measurable_pi_apply (vOf X τ))

theorem measurableSet_Sg : MeasurableSet (Sg C) := by
  have : Sg C = ⋂ τ, (fun x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => x τ) ⁻¹'
      {y : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * Matrix.of y * C.Qi τ)} := by
    ext x; simp [Sg]
  rw [this]
  refine MeasurableSet.iInter (fun τ => measurable_pi_apply τ ?_)
  apply IsClosed.measurableSet
  unfold Formalism.REAL.inUJ
  have hm : Continuous (fun y : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => C.Q τ * Matrix.of y * C.Qi τ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact isClosed_eq ((hm.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hm) continuous_const

theorem measurable_mkUJ' {n m : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun y : (Fin m → Fin m → ℂ) => mkUJ' ε (Q * Matrix.of y * Qi)) := by
  set S : Set (Fin m → Fin m → ℂ) := {y | Formalism.REAL.inUJ ε (Q * Matrix.of y * Qi)} with hS
  have hm : Continuous (fun y : (Fin m → Fin m → ℂ) => Q * Matrix.of y * Qi) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hSc : IsClosed S := by
    unfold Formalism.REAL.inUJ at hS
    rw [hS]
    exact isClosed_eq ((hm.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hm) continuous_const
  have hf : Continuous (fun y : S => mkUJ (ε := ε) (Q * Matrix.of (y : Fin m → Fin m → ℂ) * Qi) y.2) := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    refine ⟨hm.comp continuous_subtype_val, ?_⟩
    exact ((continuous_const.matrix_mul (hm.comp continuous_subtype_val).matrix_conjTranspose).matrix_mul
      continuous_const)
  have e : (fun y : (Fin m → Fin m → ℂ) => mkUJ' ε (Q * Matrix.of y * Qi)) =
      fun y => if hy : y ∈ S then mkUJ (ε := ε) (Q * Matrix.of y * Qi) hy else (fun _ : (Sᶜ : Set _) => (1 : Formalism.REAL.UJ ε)) ⟨y, hy⟩ := by
    funext y; rfl
  rw [e]
  exact Measurable.dite hf.measurable measurable_const hSc.measurableSet

theorem measurable_back : Measurable (back C) := by
  refine measurable_pi_lambda _ (fun v => ?_)
  exact (measurable_mkUJ' _ _ _).comp (measurable_pi_apply (X.pl v))

theorem measEmb_trI : MeasurableEmbedding (trI C) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_trI C) (by rw [range_trI]; exact measurableSet_Sg C)
    (measurable_back C) (back_trI C)

end Back

theorem isFund_trI : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u)
      (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun _ => 1)) (trI C '' Y.FN u) := by
  intro D X Y u C
  have hsub : ∀ a b, a ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u → b ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u →
      a * b⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
    intro a b ha hb
    rw [← Formalism.L2.SG.Pf.NOsub_coe X u Y.hK] at ha hb ⊢
    exact Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)
  obtain ⟨hFm, hcov, hstr⟩ := Y.FN_fund u
  refine ⟨(measEmb_trI C).measurableSet_image.2 hFm, fun x hx => ?_⟩
  have hxS : x ∈ Sg C := fun τ =>
    inUJ_conj _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _ (hx τ).1.1
  have hy : trI C (back C x) = x := trI_back C hxS
  obtain ⟨s, hs, hsF⟩ := hcov (back C x)
  refine ⟨trI C s, ⟨⟨s, hs, rfl⟩, ?_⟩, ?_⟩
  · rw [← hy, ← trI_mul]
    exact ⟨_, hsF, rfl⟩
  · rintro m ⟨⟨s', hs', rfl⟩, ⟨f, hf, hfe⟩⟩
    rw [← hy, ← trI_mul] at hfe
    have e : f = s' * back C x := trI_inj C hfe
    rw [e] at hf
    have h1 := hstr _ hsF (s' * s⁻¹) (hsub _ _ hs' hs) (by rwa [mul_assoc, inv_mul_cancel_left])
    rw [mul_inv_eq_one.1 h1]

end GlobalTheory.TypeAsm.CovTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentActionCocycle
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisLaw

open GlobalTheory.BesselCompare GlobalTheory.RootExch GlobalTheory.BesselClosed

variable {D : D7} {L A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem rat_decomp (d : FJDat L A B ι) (v : B.V) :
    ∃ (c : Fin d.ρ → D.host.E) (a : A.V) (c' : Fin d.ρ → D.host.E), v = ∑ l, c l • d.e l + ι a + ∑ l, c' l • d.f l := by
  let Φ : ((Fin d.ρ → D.host.E) × A.V × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
    (Fintype.linearCombination D.host.E d.e).coprod (ι.coprod (Fintype.linearCombination D.host.E d.f))
  have hΦ : ∀ c a c', Φ (c, a, c') = ∑ l, c l • d.e l + ι a + ∑ l, c' l • d.f l := fun c a c' => by
    simp [Φ, Fintype.linearCombination_apply, add_assoc]
  have sw : ∀ x y : B.V, B.hT y x = star (B.hT x y) := fun x y => (B.herm.eq _ _).symm
  have ef : ∀ i l, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun i l => d.ef l i
  have fe : ∀ i l, B.hT (d.e i) (d.f l) = if l = i then 1 else 0 := fun i l => by
    rw [sw, ef]; by_cases h : i = l
    · simp [h]
    · simp [h, Ne.symm h]
  have ee : ∀ i l, B.hT (d.e i) (d.e l) = 0 := fun i l => d.ee l i
  have ff : ∀ i l, B.hT (d.f i) (d.f l) = 0 := fun i l => d.ff l i
  have eA : ∀ i x, B.hT (d.e i) (ι x) = 0 := fun i x => hD_swap_zero (d.eA i x)
  have fA : ∀ i x, B.hT (d.f i) (ι x) = 0 := fun i x => hD_swap_zero (d.fA i x)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    rintro ⟨c, a, c'⟩ h
    rw [hΦ] at h
    have h1 : c = 0 := funext fun i => by simpa [map_sum, ef, ff, fA] using congrArg (B.hT (d.f i)) h
    have h2 : c' = 0 := funext fun i => by simpa [map_sum, fe, ee, eA] using congrArg (B.hT (d.e i)) h
    subst h1 h2
    have h3 : ι a = 0 := by simpa using h
    have h4 : a = 0 := A.nondeg.1 a fun y => by rw [← d.isom a y, h3]; simp
    rw [h4]; rfl
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  have hs : Function.Surjective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    have := d.codim
    simp only [Module.finrank_prod, Module.finrank_fin_fun, A.rank_eq, B.rank_eq]
    omega)).1 hinj
  obtain ⟨⟨c, a, c'⟩, h⟩ := hs v
  exact ⟨c, a, c', by rw [← h, hΦ]⟩

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_sum {ρ : ℕ} (c : Fin ρ → D.host.E) (e : Fin ρ → B.V) :
    vecA B (∑ l, c l • e l) = ∑ l, incA D (c l) • vecA B (e l) := by
  funext k; simp [vecA, map_sum]

theorem iA_eq (s : Fin A.rank → AE D) : iA ι s = ∑ l, s l • vecA B (ι (A.frame l)) := by
  rw [iA, frameMat_eq, eMat_mulVec]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA_eq]
  conv_lhs => rw [← A.frame.sum_repr a]
  simp only [map_sum, map_smul]
  rw [vecA_sum]
  rfl

theorem eq_sum_frame (x : Fin B.rank → AE D) : x = ∑ k, x k • vecA B (B.frame k) := by
  funext j
  simp [vecA, Finsupp.single_apply, apply_ite (incA D)]

theorem ad_decomp (d : FJDat L A B ι) (x : Fin B.rank → AE D) :
    ∃ (c : Fin d.ρ → AE D) (a : Fin A.rank → AE D) (c' : Fin d.ρ → AE D),
      x = ∑ l, c l • vecA B (d.e l) + iA ι a + ∑ l, c' l • vecA B (d.f l) := by
  let Φ : ((Fin d.ρ → AE D) × (Fin A.rank → AE D) × (Fin d.ρ → AE D)) →ₗ[AE D] (Fin B.rank → AE D) :=
    (Fintype.linearCombination (AE D) fun l => vecA B (d.e l)).coprod
      (((frameMat B A ι).map (incA D)).mulVecLin.coprod (Fintype.linearCombination (AE D) fun l => vecA B (d.f l)))
  have hΦ : ∀ c a c', Φ (c, a, c') = ∑ l, c l • vecA B (d.e l) + iA ι a + ∑ l, c' l • vecA B (d.f l) := fun c a c' => by
    simp only [Φ, LinearMap.coprod_apply, Fintype.linearCombination_apply, add_assoc, Matrix.mulVecLin_apply, iA]
  have hx : x ∈ LinearMap.range Φ := by
    rw [eq_sum_frame x]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    obtain ⟨c, a, c', h⟩ := rat_decomp d (B.frame k)
    refine ⟨(fun l => incA D (c l), vecA A a, fun l => incA D (c' l)), ?_⟩
    rw [hΦ, h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota]
  obtain ⟨⟨c, a, c'⟩, h⟩ := hx
  exact ⟨c, a, c', by rw [← h, hΦ]⟩

variable (d : FJDat L A B ι)

theorem mem_NS {n : GA D B} (hn : n ∈ d.N) : n ∈ NS B d.e := by
  rw [← closure_NS, SetLike.mem_coe, ← NFlag_eMat]; exact hn

theorem lower {n : GA D B} (hn : n ∈ d.N) {k : ℕ} {v} (hv : v ∈ spanLt B d.e (k + 1)) :
    (mt B n).mulVec v - v ∈ spanLt B d.e k := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [← Matrix.mulVecLin_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, ← smul_sub]
  rcases lt_or_ge l.1 (k + 1) with hl | hl
  · exact Submodule.smul_mem _ _ (spanLt_mono (by omega) ((mem_NS_iff.1 (mem_NS d hn)).1 l))
  · rw [hc l hl, zero_smul]; exact zero_mem _

theorem lower_iA {n : GA D B} (hn : n ∈ d.N) (a) : (mt B n).mulVec (iA ι a) - iA ι a ∈ spanLt B d.e d.ρ := by
  rw [iA_eq, ← Matrix.mulVecLin_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ _ ((mem_NS_iff.1 (mem_NS d hn)).2 _ fun i => hD_swap_zero (d.eA i _))

theorem hA_zero_swap {x y : Fin B.rank → AE D} (h : hA B x y = 0) : hA B y x = 0 := by
  rw [← hA_herm, h, map_zero]

theorem hA_span_of {k : ℕ} {v y} (hv : v ∈ spanLt B d.e k) (h : ∀ l : Fin d.ρ, l.1 < k → hA B (vecA B (d.e l)) y = 0) :
    hA B v y = 0 := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [hA_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hA_smul]
  rcases lt_or_ge l.1 k with hl | hl
  · rw [h l hl, mul_zero]
  · rw [hc l hl, zero_mul]

theorem hA_span_iA {k : ℕ} {v} (hv : v ∈ spanLt B d.e k) (a) : hA B v (iA ι a) = 0 :=
  hA_span_of d hv fun l _ => hA_vec_iA (d.eA l) a

theorem hA_span_span {k k' : ℕ} {v w} (hv : v ∈ spanLt B d.e k) (hw : w ∈ spanLt B d.e k') : hA B v w = 0 :=
  hA_span_of d hv fun l _ => hA_zero_swap (hA_span_of d hw fun j _ => by rw [hA_vec, d.ee, map_zero])

theorem hD_e_fTop (l : Fin d.ρ) : B.hD (d.e l) d.fTop = if l.1 + 1 = d.ρ then 1 else 0 := by
  have ef : ∀ i, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun i => d.ef l i
  unfold HSpace.hD
  rw [FJDat.fTop, map_sum, LinearMap.sum_apply, Finset.sum_eq_single l]
  · split_ifs
    · rw [ef, if_pos rfl]
    · rw [map_zero, LinearMap.zero_apply]
  · intro i _ hi
    split_ifs
    · rw [ef, if_neg hi.symm]
    · rw [map_zero, LinearMap.zero_apply]
  · exact fun hl => absurd (Finset.mem_univ l) hl

theorem hA_span_fTop {v} (hv : v ∈ spanLt B d.e (d.ρ - 1)) : hA B v (vecA B d.fTop) = 0 :=
  hA_span_of d hv fun l hl => by rw [hA_vec, hD_e_fTop, if_neg (by omega), map_zero]

theorem hA_fTop_iA (a) : hA B (vecA B d.fTop) (iA ι a) = 0 :=
  hA_vec_iA (fun x => d.hD_fTop _ fun l => d.fA l x) a

theorem hA_fTop_fTop : hA B (vecA B d.fTop) (vecA B d.fTop) = 0 := by
  rw [hA_vec, d.hD_fTop _ fun i => hD_swap_zero (d.hD_fTop _ fun j => d.ff j i), map_zero]

theorem vecA_fTop : vecA B d.fTop = ∑ l : Fin d.ρ, (if l.1 + 1 = d.ρ then (1 : AE D) else 0) • vecA B (d.f l) := by
  have : d.fTop = ∑ l : Fin d.ρ, (if l.1 + 1 = d.ρ then (1 : D.host.E) else 0) • d.f l :=
    Finset.sum_congr rfl fun l _ => by split_ifs <;> simp
  rw [this, vecA_sum]
  exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp

theorem sum_mem_span (b : Fin d.ρ → AE D) : ∑ l, b l • vecA B (d.e l) ∈ spanLt B d.e d.ρ :=
  ⟨b, fun l hl => absurd l.2 (by omega), rfl⟩

theorem act_fTop {n : GA D B} (hn : n ∈ d.N) : ∃ b : Fin d.ρ → AE D,
    actV B n d.fTop = vecA B d.fTop + iA ι (d.aCo n) + ∑ l, b l • vecA B (d.e l) := by
  obtain ⟨c, a, c', h⟩ := ad_decomp d (actV B n d.fTop)
  have fe : ∀ i j, B.hD (d.f i) (d.e j) = if i = j then 1 else 0 := fun i j => by
    have h1 : B.hD (d.f i) (d.e j) = star (B.hD (d.e j) (d.f i)) := (B.herm.eq _ _).symm
    rw [h1, d.ef]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : ∀ j : Fin d.ρ, c' j = if j.1 + 1 = d.ρ then 1 else 0 := fun j => by
    have h1 : hA B (actV B n d.fTop) (vecA B (d.e j)) = c' j := by
      rw [h, hA_add, hA_add, hA_coeff B d.f d.e fe, hA_zero_swap (hA_vec_iA (d.eA j) a),
        hA_span_span d (sum_mem_span d c) (vec_mem_spanLt j.2), zero_add, zero_add]
    have h2 := hA_span_fTop d (spanLt_mono (by have := j.2; omega)
      (lower d (inv_mem hn) (vec_mem_spanLt (B := B) (e := d.e) (l := j) (Nat.lt_succ_self _))))
    rw [hA_sub, sub_eq_zero, hA_vec, hD_e_fTop] at h2
    rw [← h1, actV, hA_mt_left, ← hA_herm, h2]
    split_ifs <;> simp
  have h' : actV B n d.fTop = vecA B d.fTop + iA ι a + ∑ l, c l • vecA B (d.e l) := by
    rw [h, vecA_fTop]; simp only [hc]; abel
  exact ⟨c, by rw [(d.coords_of n a c h').1]; exact h'⟩

theorem span_pred {n : GA D B} (hn : n ∈ d.N) {v} (hv : v ∈ spanLt B d.e d.ρ) :
    (mt B n).mulVec v - v ∈ spanLt B d.e (d.ρ - 1) :=
  lower d hn (spanLt_mono (by omega) hv)

theorem aCo_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) : d.aCo (n * n') = d.aCo n + d.aCo n' := by
  obtain ⟨b, h⟩ := act_fTop d hn
  obtain ⟨b', h'⟩ := act_fTop d hn'
  obtain ⟨c, -, hc⟩ := add_mem (add_mem (sum_mem_span d b) (lower_iA d hn (d.aCo n')))
    (add_mem (spanLt_mono (Nat.sub_le _ _) (span_pred d hn (sum_mem_span d b'))) (sum_mem_span d b'))
  refine (d.coords_of _ _ c ?_).1
  change _ = _ + iA ι _ + _
  unfold actV at h h' ⊢
  rw [mulVec_mul, h', Matrix.mulVec_add, Matrix.mulVec_add, h, ← hc, iA_add]
  abel

theorem tCo_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) :
    d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) := by
  obtain ⟨b, h⟩ := act_fTop d hn
  obtain ⟨b', h'⟩ := act_fTop d hn'
  have hs := lower_iA d hn (d.aCo n')
  have h1 := hA_span_fTop d (span_pred d hn (sum_mem_span d b'))
  rw [hA_sub, sub_eq_zero] at h1
  have h2 : d.tCo n' = hA B (∑ l, b' l • vecA B (d.e l)) (vecA B d.fTop) := by
    rw [FJDat.tCo, h', hA_add, hA_add, hA_fTop_fTop, hA_zero_swap (hA_fTop_iA d _), zero_add, zero_add]
  have h3 := hA_mt n (iA ι (d.aCo n')) (vecA B d.fTop)
  have h4 := hA_span_iA d hs (d.aCo n)
  have h5 := hA_span_span d hs (sum_mem_span d b)
  rw [hA_sub, sub_eq_zero] at h4 h5
  rw [hA_iA d.isom] at h4
  rw [hA_zero_swap (hA_span_iA d (sum_mem_span d b) _)] at h5
  unfold actV at h
  rw [h, hA_add_right, hA_add_right, h4, h5, hA_zero_swap (hA_fTop_iA d _)] at h3
  have h6 : d.tCo (n * n') = d.tCo n + hA B ((mt B n).mulVec (iA ι (d.aCo n'))) (vecA B d.fTop) + d.tCo n' := by
    unfold actV at h'
    rw [h2, ← h1, FJDat.tCo, FJDat.tCo, actV, actV, mulVec_mul, h', Matrix.mulVec_add, Matrix.mulVec_add, hA_add, hA_add]
  linear_combination h6 + h3

theorem simple_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) (i j : Fin d.ρ) (hij : j.1 = i.1 + 1) :
    hA B (actV B (n * n') (d.e j)) (vecA B (d.f i)) =
      hA B (actV B n (d.e j)) (vecA B (d.f i)) + hA B (actV B n' (d.e j)) (vecA B (d.f i)) := by
  have h1 := (mem_NS_iff.1 (mem_NS d hn')).1 j
  rw [hij] at h1
  have h2 := ((mem_spanLt_iff d.ef).1 (lower d hn h1)).1 i le_rfl
  rw [hA_sub, hA_sub, hA_vec, d.ef, if_neg (fun e => by subst e; omega), map_zero, Matrix.mulVec_sub, hA_sub] at h2
  unfold actV at h2 ⊢
  rw [mulVec_mul]
  linear_combination h2

theorem chr_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) (ψ : AddChar (AF D.host.F) ℂ) :
    d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n' := by
  unfold FJDat.chr
  rw [← AddChar.map_add_eq_mul, ← map_add, ← Finset.sum_add_distrib]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [simple_mul d hn hn' _ _ rfl, mul_add]

theorem law : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), ∀ n ∈ d.N, ∀ n' ∈ d.N,
    d.aCo (n * n') = d.aCo n + d.aCo n' ∧ d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) ∧
    (∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n') ∧
    ∃ b : Fin d.ρ → AE D, actV B n d.fTop =
      vecA B d.fTop + ((frameMat B A ι).map (incA D)).mulVec (d.aCo n) + ∑ l, b l • vecA B (d.e l) :=
  fun _ _ _ _ _ d _ hn _ hn' => ⟨aCo_mul d hn hn', tCo_mul d hn hn', chr_mul d hn hn', act_fTop d hn⟩

end GlobalTheory.HeisLaw

end
end

