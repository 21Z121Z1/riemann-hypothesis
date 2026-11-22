import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero
section
noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

namespace ConeMeet

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCone bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

theorem apply_sum_nsmul {L : Type} [AddCommGroup L] (F : L →ₗ[ℤ] ℤ) {p : ℕ} (n : Fin p → ℕ) (v : Fin p → L) :
    F (∑ j, n j • v j) = ∑ j, (n j : ℤ) * F (v j) := by
  simp [map_sum, map_nsmul]

theorem ray {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    (hγ' : IsCone bar φ γ') {i : Fin m} {k : ℕ} {d : Fin m' → ℕ} (hk : 0 < k) (hkd : k • γ i = ∑ j, d j • γ' j)
    (hback : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • γ' j = ∑ l, e l • γ l) :
    ∃ j, γ i = γ' j := by
  classical
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf : ∀ a b, f a (g b) = if a = b then 1 else 0 := hf
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have H1 : k • g i = ∑ j, d j • g' j := Subtype.ext (by simpa [g, g', Submodule.coe_sum] using hkd)
  have H2 : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := hback j hj
    exact ⟨kj, e, hkj, Subtype.ext (by simpa [g, g', Submodule.coe_sum] using he)⟩

  have coord : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l ∧
      ∀ l, (kj : ℤ) * f l (g' j) = e l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := H2 j hj
    refine ⟨kj, e, hkj, he, fun l => ?_⟩
    have t := congrArg (f l) he
    rw [map_nsmul, apply_sum_nsmul] at t
    simpa [hf] using t
  have Z : ∀ l, l ≠ i → ∀ j, d j ≠ 0 → f l (g' j) = 0 := by
    intro l hl
    have s := congrArg (f l) H1
    rw [map_nsmul, apply_sum_nsmul, hf, if_neg hl, smul_zero] at s
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (d j : ℤ) * f l (g' j) := fun j _ => by
      by_cases hd : d j = 0
      · simp [hd]
      · obtain ⟨kj, e, hkj, -, he⟩ := coord j hd
        have : 0 ≤ (kj : ℤ) * f l (g' j) := (he l).symm ▸ Int.natCast_nonneg _
        exact mul_nonneg (Int.natCast_nonneg _) ((mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 this)
    intro j hd
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 s.symm j (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : k • g i = 0 := by rw [H1]; simp [hc]
    have s := congrArg (f i) this
    rw [map_nsmul, hf, if_pos rfl, map_zero] at s
    simp at s
    omega
  obtain ⟨kj, e, hkj, he, hc⟩ := coord j hj
  have hel : ∀ l, l ≠ i → e l = 0 := fun l hl => by
    have := hc l
    rw [Z l hl j hj, mul_zero] at this
    exact_mod_cast this.symm
  have he' : kj • g' j = e i • g i := by
    rw [he, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  have t := congrArg (f' j) he'
  rw [map_nsmul, map_nsmul, hf', if_pos rfl] at t
  simp only [nsmul_eq_mul, mul_one] at t
  have hx := hc i
  have hx0 : 0 ≤ f i (g' j) := (mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 (hx ▸ Int.natCast_nonneg _)
  have hxy : f i (g' j) * f' j (g i) = 1 := by
    have : (kj : ℤ) * (f i (g' j) * f' j (g i)) = kj * 1 := by
      rw [← mul_assoc, hx, mul_one]; exact_mod_cast t.symm
    exact mul_left_cancel₀ (by exact_mod_cast hkj.ne') this
  have hx1 : f i (g' j) = 1 := Int.eq_one_of_mul_eq_one_right hx0 hxy
  have hei : e i = kj := by rw [hx1, mul_one] at hx; exact_mod_cast hx.symm
  rw [hei] at he'
  refine ⟨j, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ (congrArg Subtype.val he') a b
  simp [g, g'] at this
  rcases this with h | h
  · exact h.symm
  · omega

theorem mem_of_coeff_ne_zero {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X}
    (hγ : IsCone bar φ γ) (hγ' : IsCone bar φ γ') {c : Fin m → ℝ} {c' : Fin m' → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc' : ∀ j, 0 ≤ c' j) (hrel : ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j)) (i : Fin m) (hi : c i ≠ 0) :
    ∃ j, γ i = γ' j := by
  classical
  obtain ⟨k, d, hk, hkd⟩ := inCone hγ' hγ.mem hγ.nonneg hc hc' ((linearOn_iff φ γ).1 hγ.linear c hc) hrel i hi
  refine ray hγ hγ' hk hkd fun j hj => ?_
  refine inCone (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hγ hγ'.mem hγ'.nonneg
    (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
    ((linearOn_iff φ γ').1 hγ'.linear _ fun j => Nat.cast_nonneg _) ?_ j (by exact_mod_cast hj)
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ hkd a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
  simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  exact_mod_cast this.symm

end ConeMeet

open ConeMeet in

theorem cone_meet : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) (c' : Fin m' → ℝ), IsCone bar φ γ → IsCone bar φ γ' → (∀ i, 0 ≤ c i) → (∀ j, 0 ≤ c' j) →
    ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j) → ∀ i, c i ≠ 0 → ∃ j, γ i = γ' j ∧ c i = c' j := by
  intro O _ bar φ X _ _ _ m m' γ γ' c c' hγ hγ' hc hc' hrel i hi
  classical
  obtain ⟨j, hj⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel i hi
  refine ⟨j, hj, ?_⟩
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have s := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms bar X).subtype) Subtype.val_injective (f' j)
    (β := Sum.elim g g') (c := Sum.elim c (-c')) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Submodule.subtype_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
        g, g', hrel, add_neg_cancel])
  rw [Fintype.sum_sum_type] at s
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hf', Int.cast_ite,
    Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at s
  have h1 : ∑ l, c l * (f' j (g l) : ℝ) = c i := by
    rw [Finset.sum_eq_single i]
    · have : g i = g' j := Subtype.ext hj
      rw [this, hf', if_pos rfl, Int.cast_one, mul_one]
    · intro l _ hl
      by_cases hcl : c l = 0
      · rw [hcl, zero_mul]
      · obtain ⟨p, hp⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel l hcl
        have : g l = g' p := Subtype.ext hp
        rw [this, hf', if_neg, Int.cast_zero, mul_zero]
        rintro rfl
        exact hl (hγ.injective (hp.trans hj.symm))
    · simp
  linarith

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.L2.Forms Formalism.L2.G Formalism.UG Matrix
open scoped TensorProduct

section Hyp

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

set_option maxHeartbeats 2000000 in

theorem stab_iff_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hdual : SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β))
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β)
      (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Hyp

section Main

set_option maxHeartbeats 8000000 in

theorem stepTiesD_mid : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ u v hg i hi hi2
  have h1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
  let F := t.C.forms u
  let dt : GlobalTheory.Port.MemDt F :=
    ⟨fun j hj _ => GlobalTheory.Port.detTieOf t.full.1.base _, fun j _ _ β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hB : GlobalTheory.Port.BaseEx t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) := by
    obtain ⟨Cm, hC1, hC2, -⟩ := F.deC (i + 1) h1 hi2
    exact GlobalTheory.Port.baseEx_of t.g.herm u v hg _ Cm hC1 hC2 (GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dt i hi v hg)
  have hrat : ∀ β, Formalism.L2.G.Cmp.ChiRatAll ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev (w.D Z).what₂.embLL := by
    rw [GlobalTheory.Port.formsInMem_mid F dt i hi hi2]
    intro β
    obtain ⟨k, hR⟩ := (t.std u).mid (i + 1) h1 hi2
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i + 1) (le_of_succ_m hi2) _ _ _ rfl
      (F.ch (i + 1) h1 hi2) k hR
      (fun β => GlobalTheory.Port.chi_fin_of_glevH (F.glevC (i + 1) h1 hi2 β) fun a => ((w.D Z).host.g_prime a).ne_zero) β
  have hψ : GlobalTheory.Port.PsiEx (GlobalTheory.Port.formsInMem F dt i hi) (t.cmp.embW u v hg) :=
    GlobalTheory.Port.psiEx_of _ (t.cmp.embW u v hg) (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O hrat
      (GlobalTheory.Port.finMem_of F dt i hi)
  haveI : ∀ j, Finite (t.C.herm.base.Ch u j) := fun j => t.C.herm.base.ChFin u j
  let S : StepD t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) :=
    ⟨hB.choose, hB.choose_spec.2, fun β => (hψ β).choose, fun β => GlobalTheory.Port.fin_of _ β _⟩
  refine ⟨GlobalTheory.Port.formsInMem F dt i hi, GlobalTheory.Port.formsInMem_fin F dt i hi, S, ?_⟩
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ (GlobalTheory.Port.formsInMem F dt i hi).T := by
    rw [GlobalTheory.Port.memberChainForms_levelPrime_eq_member]; exact hg.2.2.2.2.2
  have hbad : ∀ w' ∈ (GlobalTheory.Port.formsInMem F dt i hi).bad,
      (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
    rw [GlobalTheory.Port.formsInMem_bad]; exact Formalism.L2.G.bad_notOver u v hg
  have hre := fun β w' => GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram
    (gramN (w.D Z) (i + 1) hi) (gramN_apply (w.D Z) (i + 1) hi) ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev w'
  refine ⟨fun β w' h x hx ha hb => ?_, fun β w' h x hx => ?_, hbad, hB.choose_spec.1, fun β => (hψ β).choose_spec,
    GlobalTheory.Port.chRat_mem (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 F dt i hi,
    GlobalTheory.Port.formsInMem_ok F dt i hi v, hT⟩
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    exact (hre β w').2.2 (fun hb' => hbad w' hb' h) hTw
      ((stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hx).2 ⟨ha, hb⟩)
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    have hl := (hre β w').1 hx
    exact (stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hl.1).1 hl

end Main

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerTopStepChartConditions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq

noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq.TopStep

open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.MainNotions.G.CmpJ.PStabEq Matrix
open scoped TensorProduct

section Stab

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

set_option maxHeartbeats 4000000 in

theorem stab_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hT : ¬ D.what₂.places.resChar w ∣ Fo.T)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hdual := (GlobalTheory.Port.formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi)
    (gramN_apply D (i + 1) hi) (Fo.K β).lev w').2.1 (GlobalTheory.Port.T_not_mem hg.1 hT w' h)
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Stab

set_option maxHeartbeats 4000000 in

theorem stepTies_top : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 = (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQp O hO' hunf E hE u v hg
  intro i hi h
  let F := t.C.forms u
  let dt := GlobalTheory.Port.detTieOf t.full.1.base (F.cls (i+1) hi (Or.inr h)).lev
  let Fo : FormsIn ((w.D Z).fm u) (i + 1) hi := GlobalTheory.Port.formsInOne (F.val (i+1) hi (Or.inr h)) dt
  let dtM : GlobalTheory.Port.MemDt F := ⟨fun j hj h' => GlobalTheory.Port.detTieOf t.full.1.base _, fun j h1 h2 β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hL0 := GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dtM i hi v hg
  rw [GlobalTheory.Port.formsInMem_top F dtM i hi h] at hL0
  have hL : GlobalTheory.Port.ChartBaseLatticeEqSelfDualAtP u Fo ((w.D Z).what₂.places.resChar v) := hL0
  obtain ⟨Cm, h1, h2, -⟩ := (F.val (i+1) hi (Or.inr h)).de
  obtain ⟨B0, hstd, hB⟩ := GlobalTheory.Port.baseEx_of t.g.herm u v hg Fo Cm h1 h2 hL
  haveI : IsFractionRing ((w.D Z).gat u v hg).O ((w.D Z).gat u v hg).Kf :=
    (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O
  have hfin := GlobalTheory.Port.chi_fin_top F (i + 1) hi h
  have hrat : Formalism.L2.G.Cmp.ChiRatAll (F.cls (i+1) hi (Or.inr h)).lev (w.D Z).what₂.embLL := by
    obtain ⟨k, hR⟩ := (t.std u).ends (i+1) hi (Or.inr h)
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i+1) hi (badG (w.D Z)) (fun _ => ())
      _ rfl (fun β => Formalism.MainNotions.G.CmpJ.oneChart (F.cls (i+1) hi (Or.inr h)) β) k hR (fun _ => hfin) ()
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Mem.Top.KerTwPsi.exists_psiTiedJ hi (F.cls (i+1) hi (Or.inr h)).lev
    (Formalism.MainNotions.G.ChartsLv.sameU_of Fo ()) (t.cmp.embW u v hg) hrat hfin
  let S : StepD t.g.herm u v hg Fo :=
    { B := B0
      B_lat := fun _ => hB ()
      ψ := fun _ => ψ
      fin := fun β => GlobalTheory.Port.fin_of Fo β _ }
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ Fo.T := hg.2.2.2.2.2
  refine ⟨Fo, (inferInstance : Finite Unit), S, ?_, ?_, ?_, hstd, fun _ => hψ, ?_, trivial, hT⟩
  · intro β w' hw x hx hx1 hx2
    exact (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').2.2 (fun hb => Formalism.L2.G.bad_notOver u v hg w' hb hw)
      (GlobalTheory.Port.T_not_mem hg.1 hT w' hw) ((stab_frB Fo S β w' hw hT x hx).2 ⟨hx1, hx2⟩)
  · intro β w' hw x hx
    have hle := (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').1 hx
    exact (stab_frB Fo S β w' hw hT x hle.1).1 hle
  · exact Formalism.L2.G.bad_notOver u v hg
  · intro β cl
    exact GlobalTheory.Port.chRat_ofChiD (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 _ _ _

end GlobalTheory.Mem.Top.KerOne.CertEq.TopStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluckerVector_blockTriangular_frame_change : ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (c c' : Let m → Fin (M + 1) → S) (d : Let m → S) (k : ℕ) (e : Fin k → Let m), Tri c c' d → Down e → plk c' e = (∏ l, d (e l)) • plk c e := by
  first | exact @GlobalTheory.FlagEmb.plk_tri | exact GlobalTheory.FlagEmb.plk_tri | (intros; apply GlobalTheory.FlagEmb.plk_tri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolArc

theorem injective_of_charZero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) (W : ValuationSubring ℂ) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    (b' : c.V W →+* O') : Function.Injective b' := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have hvF : ((v : c.F)) ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := ((v : c.F))⁻¹)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))
  have hint' : IsIntegral (c.V W) (n • ((v : c.F))⁻¹) := hint.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hw' : (w : c.F) = (n : c.F) * (v : c.F)⁻¹ := by rw [← zsmul_eq_mul]; exact hw
  have e : (n : c.V W) = v * w := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, hw', mul_comm (n : c.F), ← mul_assoc, mul_inv_cancel₀ hvF, one_mul]
    simp
  have h0 : b' (n : c.V W) = 0 := by rw [e, map_mul, hv, zero_mul]
  rw [map_intCast] at h0
  exact hn (Int.cast_eq_zero.mp h0)

end GlobalTheory.PolArc

theorem GlobalTheory.PolArc.generic_factors_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) (O' : Type) [CommRing O'] [IsDomain O']
    [CharZero O'] (b' : c.V W →+* O') (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
    χ₀ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b' →
    (∀ x : Sp (PowerSeries O'), χ₀ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) →
    ∃ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j := by
  intro E _ _ _ H D l Xo c W Y O' _ _ _ b' χ₀ hs hab
  have hb' := GlobalTheory.PolArc.injective_of_charZero c W b'
  have hC : Function.Injective (PowerSeries.C (R := O')) := fun a b h => by
    simpa using congrArg (PowerSeries.constantCoeff (R := O')) h
  have hinj : Function.Injective ((algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))).comp
      ((PowerSeries.C (R := O')).comp b')) :=
    (IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))).comp (hC.comp hb')
  obtain ⟨g, hg⟩ : ∃ g : c.F →+* FractionRing (PowerSeries O'), g.comp (c.V W).subtype =
      (algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))).comp ((PowerSeries.C (R := O')).comp b') := by
    refine ⟨IsFractionRing.lift (A := c.V W) (K := c.F) hinj, RingHom.ext fun v => ?_⟩
    have key := IsFractionRing.lift_algebraMap (A := c.V W) (K := c.F) hinj v
    rw [RingHom.comp_apply]
    exact key
  have hsq : (Out.jK (PowerSeries O') ≫ χ₀) ≫ Y.s = spMap g ≫ spMap (c.V W).subtype := by
    rw [Category.assoc, hs]
    simp only [Out.jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  let q := pullback.lift (Out.jK (PowerSeries O') ≫ χ₀) (spMap g) hsq
  have hrange : Set.range q ⊆ Set.range Y.jQ := by
    rintro _ ⟨y, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]
    intro hX
    have h1 : y.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ y.asIdeal y.isPrime
    have h2 : algebraMap (PowerSeries O') (FractionRing (PowerSeries O')) PowerSeries.X ∈ y.asIdeal := hX
    rw [h1, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h2
    exact PowerSeries.X_ne_zero h2
  haveI := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ q hrange, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
end
end

