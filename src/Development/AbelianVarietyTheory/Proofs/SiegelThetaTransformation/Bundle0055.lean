import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NsmulMemHatA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.VacBase

theorem exists_reps {G H : Type} [AddCommGroup G] [AddCommGroup H] (A B : AddSubgroup G) (A₀ : AddSubgroup H)
    (hfg : A₀.FG) (φ : H →+ G) (hφ : ∀ y ∈ A₀, φ y ∈ A) (hs : ∀ u ∈ A, ∃ y ∈ A₀, u - φ y ∈ B) (k : ℕ)
    (hN : ∀ u ∈ A, (2 * k + 1) • u ∈ B) :
    ∃ Ys : Finset G, (∀ y ∈ Ys, ∃ u ∈ A, y = 2 • u) ∧ ∀ u ∈ A, ∃! y, y ∈ Ys ∧ u - y ∈ B := by
  haveI : AddGroup.FG A₀ := (AddGroup.fg_iff_addSubgroup_fg A₀).2 hfg
  let φ' : A₀ →+ A := (φ.comp A₀.subtype).codRestrict A fun y => hφ y y.2
  have hq : ∀ a b : A, (a : A ⧸ B.addSubgroupOf A) = b ↔ (a : G) - b ∈ B := fun a b => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  have hsurj : Function.Surjective ((QuotientAddGroup.mk' (B.addSubgroupOf A)).comp φ') := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, hy, h⟩ := hs u u.2
    exact ⟨⟨y, hy⟩, ((hq _ _).2 h).symm⟩
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective hsurj
  haveI : Finite (A ⧸ B.addSubgroupOf A) := by
    refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 * k + 1, Nat.succ_pos _, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hN u u.2
  haveI := Fintype.ofFinite (A ⧸ B.addSubgroupOf A)
  let r : A ⧸ B.addSubgroupOf A → G := fun c => 2 • ((k + 1) • (c.out : G))
  have hr : ∀ (u : A) c, (u : G) - r c ∈ B ↔ (u : A ⧸ B.addSubgroupOf A) = c := fun u c => by
    have e : (u : G) - r c = ((u : G) - c.out) - (2 * k + 1) • (c.out : G) := by
      simp only [r]; module
    rw [e, sub_eq_add_neg, B.add_mem_cancel_right (B.neg_mem (hN _ c.out.2)), ← hq, QuotientAddGroup.out_eq']
  refine ⟨Finset.univ.image r, fun y hy => ?_, fun u hu => ?_⟩
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨_, A.nsmul_mem c.out.2 _, rfl⟩
  · refine ⟨r (⟨u, hu⟩ : A), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hr ⟨u, hu⟩ _).2 rfl⟩, ?_⟩
    rintro y ⟨hy, h⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(hr ⟨u, hu⟩ c).1 h]

theorem exists_odd_mem {R : Type} [CommRing R] (I : Ideal R) (h : IsCoprime I (Ideal.span {2})) (M : ℕ)
    (hM : 0 < M) (hm : (M : R) ∈ I) : ∃ k : ℕ, ((2 * k + 1 : ℕ) : R) ∈ I := by
  obtain ⟨a, m, ⟨k, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hM.ne'
  refine ⟨k, ?_⟩
  have h2 : IsCoprime I (Ideal.span {(2 : R) ^ a}) := by
    rw [← Ideal.span_singleton_pow]; exact h.pow_right
  obtain ⟨i, hi, j, hj, e⟩ := Ideal.isCoprime_iff_exists.1 h2
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hj
  have : ((2 * k + 1 : ℕ) : R) = i * ((2 * k + 1 : ℕ) : R) + c * ((2 ^ a * (2 * k + 1) : ℕ) : R) := by
    rw [Nat.cast_mul (2 ^ a), ← mul_assoc, ← add_mul, Nat.cast_pow, Nat.cast_ofNat, e, one_mul]
  rw [this]
  exact I.add_mem (I.mul_mem_right _ hi) (I.mul_mem_left _ hm)

theorem nsmul_mem_hatA {D : D7} (S T : HSp D) (Λ : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank) (N : ℕ)
    (h : ∀ v ∈ L, N • v ∈ L') : ∀ u ∈ hatA S T (tens Λ L), N • u ∈ hatA S T (tens Λ L') := by
  have h1 : tens Λ L ≤ (tens Λ L').comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    exact AddSubgroup.subset_closure ⟨v, hv, N • u, h u hu, (map_nsmul (LatTens.vmv v) N u).symm⟩
  have h2 : hatA S T (tens Λ L) ≤ (hatA S T (tens Λ L')).comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, y, hy, rfl⟩
    exact AddSubgroup.subset_closure ⟨α, hα, N • y, h1 hy, (map_nsmul (LatTens.gen S T α) N y).symm⟩
  exact fun u hu => h2 hu

theorem vac_base : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ LT : Lt D.host.E T.rank, IsAA C.X.Λ LT → ∀ f₀, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) ((stdL D.host.E S.rank) : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) f₀ → C.IsTh f₀ ∧ f₀ ≠ 0 ∧ C.IsFock B f₀ ∧ IsLatVac (heisO C.ψ S T) (hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)) f₀ ∧ ∃ Ys : Finset (WO S T), (∀ y ∈ Ys, ∃ u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)), y = 2 • u) ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)), ∃! y, y ∈ Ys ∧ u - y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
  intro D S T C μ 𝓕 hμ Lv hn M _ hM hm B _ LT hLT f₀ hf
  obtain ⟨-, hv⟩ := hf
  have hstar : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := by
    have : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank → star v ∈ stdL D.host.E S.rank := fun v hv =>
      (SW.Base.mem_stdL _).2 fun a => SW.Base.isIntegral_cc ((SW.Base.mem_stdL _).1 hv a)
    exact fun v => ⟨this v, fun h => by simpa using this _ h⟩
  refine ⟨hv.theta, ?_, hv.fock, ?_, ?_⟩
  · rintro rfl
    have := hv.norm.2 (μ, 𝓕) hμ
    simp [nrm2] at this
  · rw [← LatTens.latO_eq_hatA D S T C _ _ LT _ hstar hLT]
    exact hv.lat
  obtain ⟨k, hk⟩ := exists_odd_mem _ Lv.odd M hM hm
  have hlev := SW.level_laws _ _ C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  have hsd : SelfD C.X (Lv.sh C.X.Λ) := (hlev.2.2.2.1 _ hlev.1).1
  have hfg := (SW.TensLat.tens_selfDual_semichar_index _ _ C.X C.g C.bas C.idx S.rank C.sympl C.even Lv.w
    Lv.w_int Lv.w_tr _ hsd M _ (SW.Base.stdL_mem_Vset S.rank M)).1
  have hN : ∀ v ∈ Lv.sh C.X.Λ, (2 * k + 1) • v ∈ C.X.Λ := fun v hv => by
    have hc : ((2 * k + 1 : ℕ) : 𝓞 D.host.E) ∈ conjI Lv.𝔪 :=
      Ideal.subset_span ⟨_, hk, by simp only [RingOfIntegers.coe_eq_algebraMap, map_natCast, cc]⟩
    have := Submodule.smul_le_right (hv _ hc)
    rwa [Nat.cast_smul_eq_nsmul] at this
  have hspan : Submodule.span D.host.E (Lv.sh C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← C.X.Λ_span, Submodule.span_le]
    intro v hv
    have h1 : (M : 𝓞 D.host.E) • v ∈ Lv.sh C.X.Λ := fun b _ => by
      rw [smul_comm]
      exact Submodule.smul_mem_smul hm (C.X.Λ.smul_mem b hv)
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E] at h1
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hM.ne')).1 (Submodule.subset_span h1)
  have hspanS : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, by simp⟩
  have hh := HatLat.hatA_tens D S T C _ _ ⟨(SW.Base.stdL_mem_Vset S.rank M).1, hspanS⟩ ⟨hsd.1, hspan⟩
  have hN' := nsmul_mem_hatA S T (stdL D.host.E S.rank) _ _ _ hN
  refine exists_reps _ _ _ hfg (LatTens.gen S T 1) (fun y hy => (hh.2.1 y).2 hy) (fun u hu => ?_) k hN'
  obtain ⟨y, hy, u', hu', e⟩ := (hh.2.2.1 u hu).2 (2 * k + 1) (Nat.succ_pos _)
  refine ⟨y, hy, ?_⟩
  have : u - LatTens.gen S T 1 y = (2 * k + 1) • u' := by
    rw [e]; exact add_sub_cancel_left _ _
  rw [this]
  exact hN' u' hu'

end GlobalTheory.Ker.VacBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormMatch

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P = 1) (hP' : P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  subst hP hP'
  rw [sum_four_eq_trace, sum_four_eq_trace]
  have hk1 : (k.map σ)ᵀ * k = 1 := by simpa only [Matrix.mul_one] using hk
  have hk2 : k * (k.map σ)ᵀ = 1 := mul_eq_one_comm.mp hk1
  have hg' : ∀ R : Matrix (Fin m) (Fin n) A, (g.map σ)ᵀ * (Q * (g * R)) = Q * R := by
    intro R
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.one_mul, Matrix.mul_assoc, hg']
  conv_lhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hk2, Matrix.mul_one]

theorem sum_one_four {A : Type} [CommRing A] {m n : ℕ} (u : Fin m → Fin n → A) (Q : Fin m → Fin m → A)
    (x : Fin m → Fin n → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, (1 : Matrix (Fin n) (Fin n) A) a b * u c b * Q c d * x d a =
      ∑ k, ∑ d, ∑ c, x d k * Q c d * u c k := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single a (fun b hb => by simp [Matrix.one_apply_ne (Ne.symm hb)])]
  simp only [Matrix.one_apply_eq, one_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

variable {D : D7} {S T : HSp D}

theorem hO_actO (hS : S.gram = 1) (h : GA D S) (g : GA D T) (w w' : WO S T) :
    hO S T (actO S T h g w) (actO S T h g w') = hO S T w w' := by
  have hinv : ((HSpace.gram S)⁻¹).map (incA D) = 1 := by
    rw [hS, Matrix.inv_eq_left_inv (Matrix.mul_one 1), Matrix.map_one _ (map_zero _) (map_one _)]
  have key := sum_unitary (cA D) ((HSpace.gram T).map (incA D)) (Formalism.L2.Theta.mt T g)
    (((HSpace.gram S)⁻¹).map (incA D)) 1 (Formalism.L2.Theta.mt S h⁻¹) hinv rfl ?hg ?hk w w'
  · unfold hO actO
    simpa only [Matrix.map_apply] using key
  · have hu := g.2
    exact hu
  · have hu : ((Formalism.L2.Theta.mt S h⁻¹).map (cA D))ᵀ * (HSpace.gram S).map (incA D) * Formalism.L2.Theta.mt S h⁻¹ =
        (HSpace.gram S).map (incA D) := (h⁻¹).2
    have h1 : (HSpace.gram S).map (incA D) = 1 := by
      rw [hS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hu
    exact hu

theorem hRat_eq (C : Ctx S T) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ = ∑ k, herm C.X.Gm (y k) (y' k) := by
  unfold GlobalTheory.LatVac.hRat ReciprocityTheory.ChartRestriction.G.FD.herm
  rw [C.m.gS, C.m.gT, Matrix.inv_eq_left_inv (Matrix.mul_one 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_eq_single k (fun b hb => by simp [Matrix.one_apply_ne (Ne.symm hb)])]
  simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  have hs : star (y' k c) = ReciprocityTheory.ChartRestriction.G.FD.cc (y' k c) := rfl
  rw [hs]
  ring

theorem sum_EF (C : Ctx S T) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ)) := by
  simp only [GlobalTheory.ThFr.EF_def]
  rw [← map_sum, ← Finset.mul_sum, ← hRat_eq C, C.m.ka, Algebra.trace_trace,
    show -(2 * D.host.xi0 / 2) * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ = -(D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ) by ring,
    map_neg]

theorem symplO_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S M) (ratW T S N) = algebraMap D.host.F (AF D.host.F)
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) := by
  rw [← (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 (ratW T S M) (ratW T S N)]
  have h2 : symplOH S T (ratW T S M) (ratW T S N) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) :=
    GlobalTheory.OrientedFormLaws.symplOH_rat M N
  rw [h2, ← map_add]
  congr 1
  ring

theorem re_match {m n : ℕ} (ξ : ℂ) (Q : Fin m → Fin m → ℂ) (x y : Fin m → Fin n → ℂ) :
    ∑ k, 2 * (conj (-ξ) * ∑ a, ∑ b, conj (x a k) * conj (Q b a) * conj (conj (y b k))).re =
      -(2 * (ξ * ∑ k, ∑ d, ∑ c, x d k * Q c d * conj (y c k)).re) := by
  have key : ∀ k, conj (-ξ) * ∑ a, ∑ b, conj (x a k) * conj (Q b a) * conj (conj (y b k)) =
      conj (-ξ * ∑ a, ∑ b, x a k * Q b a * conj (y b k)) := by
    intro k
    simp only [map_mul, map_sum, map_neg]
  simp only [key, Complex.conj_re, neg_mul, Complex.neg_re, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum]

theorem EFR_realPt (C : Ctx S T) (w w' : WO S T) :
    EFR C.X (C.realPt w) (C.realPt w') = -omO S T (piW C.θ T S w) (piW C.θ T S w') := by
  rw [omO_apply, ← Finset.sum_neg_distrib]
  unfold EFR Ctx.realPt compAt
  rw [← C.m.e.sum_comp]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hS1 : gramAt D S τ = 1 := by
    unfold gramAt
    rw [C.m.gS]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hom : -omAt S T τ (piW C.θ T S w τ) (piW C.θ T S w' τ) = ∑ k, 2 * (conj (-(tauE D τ D.host.xi0)) *
      ∑ a, ∑ b, conj (piW C.θ T S w τ a k) * conj (gramAt D T τ b a) *
        conj (conj (piW C.θ T S w' τ b k))).re := by
    rw [re_match (tauE D τ D.host.xi0) (gramAt D T τ) (piW C.θ T S w τ) (piW C.θ T S w' τ), neg_inj]
    unfold omAt hAt
    have h4 := GlobalTheory.OrientedChar.trace_four ((gramAt D S τ)⁻¹) (piW C.θ T S w' τ) (gramAt D T τ) (piW C.θ T S w τ)
    have h5 := sum_one_four (fun c b => starRingEnd ℂ (piW C.θ T S w' τ c b)) (gramAt D T τ) (piW C.θ T S w τ)
    rw [h4, hS1, Matrix.inv_eq_left_inv (Matrix.mul_one 1)]
    exact congrArg (fun s => 2 * (tauE D τ D.host.xi0 * s).re) h5
  rw [hom]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : -(2 * D.host.xi0 / 2) = -D.host.xi0 := by ring
  simp only [Equiv.symm_apply_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, C.m.e_emb τ,
    NumberField.ComplexEmbedding.conjugate_coe_eq, C.m.ka, C.m.gT, Matrix.transpose_apply, Matrix.map_apply,
    hx, map_neg]
  rfl

theorem symplO_eq_add (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := ((GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 x y).symm

theorem symplOH_finW (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    symplOH S T (finW S T y) (finW S T y') = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ))) := by
  have hf : ∀ z : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T z = GlobalTheory.LatVac.finTens 1 zᵀ :=
    fun z => rfl
  have h := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 (finW S T y) (finW S T y')
  rw [hf, hf, GlobalTheory.LatVac.symplO_finTens] at h
  simp only [one_mul] at h
  rw [hf, hf]
  have key : ∀ X Y : AF D.host.F, X + X = Y + Y → X = Y := by
    intro X Y hXY
    have h2 : (2 : D.host.F) • X = (2 : D.host.F) • Y := by rw [two_smul, two_smul, hXY]
    have h3 := congrArg (fun Z => (2 : D.host.F)⁻¹ • Z) h2
    simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), one_smul] using h3
  have hp : ∀ u v : Af D.host.F, pairA D.host.F 0 u + pairA D.host.F 0 v = pairA D.host.F 0 (u + v) := by
    intro u v
    unfold pairA
    exact Prod.ext (add_zero _) rfl
  apply key
  rw [h, hp, ← map_add]
  congr 2
  ring

theorem forms_match : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (t : D.host.F), symplO S T (ratW T S yᵀ) (ratW T S y'ᵀ) = algebraMap D.host.F (AF D.host.F) t → ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F t) ∧ (∀ w w' : WO S T, IsRealPt w → IsRealPt w' → C.ψ (symplOH S T w w') = cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w') : ℝ))) ∧ (∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.ψ (symplOH S T (finW S T y) (finW S T y')) = cexp (-(π * I * ((∑ k, EF C.X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ w u : WO S T, IsRealPt w → IsFinPt u → symplO S T w u = 0 ∧ symplO S T u w = 0) ∧ (∀ w : WO S T, symplO S T w w = 0) ∧ (∀ w w' w'' : WO S T, symplO S T (w + w') w'' = symplO S T w w'' + symplO S T w' w'' ∧ symplO S T w w' = -symplO S T w' w) ∧ (∀ (h : GA D S) (g : GA D T) (w w' : WO S T), symplO S T (actO S T h g w) (actO S T h g w') = symplO S T w w') ∧ ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.realPt (ratW T S yᵀ) = embR C.X y ∧ IsFinPt (finW S T y) ∧ IsRealPt (ratW T S yᵀ - finW S T y) ∧ ∀ y', finW S T (y + y') = finW S T y + finW S T y' := by
  intro D S T C
  have hadd := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have halt := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T
  have htr : ∀ t : D.host.F, Algebra.trace ℚ D.host.F (1 / 2 * t) = 1 / 2 * Algebra.trace ℚ D.host.F t := by
    intro t
    rw [show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul,
      smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, halt.2.2.2.1, fun w w' w'' => ⟨halt.1 w w' w'', halt.2.2.1 w w'⟩, ?_, ?_⟩
  · intro y y' t ht
    rw [symplO_rat] at ht
    have : Nontrivial (AF D.host.F) := by
      unfold AF AdeleRing
      infer_instance
    rw [sum_EF C, (algebraMap D.host.F (AF D.host.F)).injective ht]
  · intro w w' hw _
    rw [GlobalTheory.OrientedChar.char_symplOH D C.θ C.ψ C.inf C.std S T w w' (Or.inl hw), EFR_realPt C]
    congr 1
    push_cast
    ring
  · intro y y'
    rw [symplOH_finW, GlobalTheory.StdRat.stdChar_fin_rat D C.ψ C.std, sum_EF C, htr]
    congr 1
    push_cast
    ring
  · intro w u hw hu
    have h0 : symplOH S T w u = 0 := hadd.2.2.2.2.2.2.2.2 w u hw hu
    have h1 : symplO S T w u = 0 := by rw [← hadd.2.2.2.1 w u, h0, add_zero]
    exact ⟨h1, by rw [halt.2.2.1 u w, h1, neg_zero]⟩
  · intro h g w w'
    unfold symplO
    rw [hO_actO C.m.gS]
  · intro y
    refine ⟨?_, finRat_inf S T yᵀ, ?_, ?_⟩
    · funext σ k a
      unfold Ctx.realPt compAt
      obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
      rw [Equiv.symm_apply_apply]
      have e := congrFun (congrFun (congrFun (piW_ratW C.inf S T yᵀ) τ) a) k
      simp only [Matrix.map_apply, embR, C.m.e_emb τ, NumberField.ComplexEmbedding.conjugate_coe_eq]
      congr 1
    · show (ratW T S yᵀ - finW S T y).map (finPart D) = 0
      have e := finRat_fin S T yᵀ
      ext i j
      have e2 := congrFun (congrFun e i) j
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.zero_apply] at e2 ⊢
      rw [← e2]
      exact sub_self _
    · intro y'
      ext a k
      simp only [finW, Matrix.of_apply, Matrix.add_apply, TensorProduct.tmul_add]

end GlobalTheory.FormMatch
end

