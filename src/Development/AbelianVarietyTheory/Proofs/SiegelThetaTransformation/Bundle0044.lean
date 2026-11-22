import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeSupOfCoprime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShVac

theorem le_sup_of_coprime {G : Type} [AddCommGroup G] {A B C : AddSubgroup G} {s m : ℕ}
    (h : s.Coprime m) (hB : ∀ y ∈ A, s • y ∈ B) (hC : ∀ y ∈ A, m • y ∈ C) :
    A ≤ (A ⊓ B) ⊔ (A ⊓ C) := by
  intro y hy
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : y = a • s • y + b • m • y := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact AddSubgroup.add_mem_sup
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hB y hy⟩) _)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hC y hy⟩) _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ}

omit [IsCMField E] in
theorem nsmul_tens {Λ Λ' : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, ∀ u ∈ L, k • vecMulVec v u ∈ tens Λ' L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L' := by
  have : tens Λ L ≤ (tens Λ' L').comap (nsmulAddMonoidHom k) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    exact h v hv u hu
  exact fun y hy => this hy

omit [IsCMField E] in
theorem nsmul_tens_left {Λ Λ' : Lt E n} {L : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, (k : E) • v ∈ Λ') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨_, h v hv, u, hu, by
    ext i j; simp [vecMulVec_apply, _root_.mul_assoc]⟩

omit [IsCMField E] in
theorem nsmul_tens_right {Λ : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ u ∈ L, (k : 𝓞 E) • u ∈ L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ L' :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨v, hv, _, h u hu, by
    rw [Nat.cast_smul_eq_nsmul]
    ext i j; simp [vecMulVec_apply, mul_left_comm]⟩

omit [IsCMField E] in
theorem relIndex_half {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L).toAddSubgroup.relIndex (L ⊓ L').toAddSubgroup ∧
    ∀ x ∈ L', x ∈ idq P Q L → x ∈ idq P Q L' := by
  obtain ⟨a, m, hm, e⟩ := Lev.cop_iff.1 hs
  have d (x : Fin r → E) : x = a • s • x + m • x := by
    rw [← mul_smul, ← add_smul, e, one_smul]
  constructor
  · refine Lev.relIndex_eq (fun x hx => hx.1) fun x (hx : x ∈ L) => ?_
    rw [d x]
    exact AddSubgroup.add_mem_sup ⟨L.smul_mem _ (L.smul_mem _ hx), L'.smul_mem _ (h x hx)⟩
      ⟨fun b _ => Submodule.smul_mem _ b (Submodule.smul_mem_smul hm hx), L.smul_mem _ hx⟩
  · intro x hx H b hb
    rw [d (b • x)]
    exact add_mem (Submodule.smul_mem _ _ (Lev.smul_map_mem LinearMap.id h (H b hb)))
      (Submodule.smul_mem_smul hm (L'.smul_mem _ hx))

omit [IsCMField E] in

theorem relIndex_shift {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') (h' : ∀ v ∈ L', s • v ∈ L) :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L').toAddSubgroup.relIndex L'.toAddSubgroup := by
  obtain ⟨h1, h2⟩ := relIndex_half (Q := Q) hs h
  obtain ⟨h3, h4⟩ := relIndex_half (Q := Q) hs h'
  rw [h1, h3, inf_comm L' L, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (idq P Q L').toAddSubgroup]
  congr 1
  ext x
  exact and_congr_left fun hx => ⟨h2 x hx.2, h4 x hx.1⟩

theorem eq_sqrt {k t : ℝ} (ht : 0 ≤ t) (h : k * t ^ 2 = 1) : t = √(k⁻¹) ∧ 0 < t := by
  refine ⟨?_, ht.lt_of_ne ?_⟩
  · rw [← eq_inv_of_mul_eq_one_right h, Real.sqrt_sq ht]
  · rintro rfl
    simp at h

theorem smul_eq_unitv {g : ℕ} {u : TF n g} (hu : IsSB u) (h1 : SW.ip u u = 1) {a : ℂ} (ha : 0 < ‖a‖) :
    a • u = ((‖a‖ : ℝ) : ℂ) • unitv (a • u) := by
  rw [unitv, TensVac.ip_smul_left _ hu (TensVac.sb_smul _ hu), TensVac.ip_smul_right _ hu hu, h1, _root_.mul_one,
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq ha.le, smul_smul (_ : ℂ) (_ : ℂ)⁻¹,
    mul_inv_cancel₀ (by exact_mod_cast ha.ne'), one_smul]

theorem shift_vac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∃ (ρ : ℝ) (s : Lt E n → ℝ), 0 < ρ ∧ ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v → ∃ t : ℂ, ‖t‖ = ρ ∧ ∀ Λ ∈ Vset E n M, 0 < s Λ ∧ projA X bas D.w (tens Λ (D.sh L)) (projA X bas D.w (tens Λ L) v) = (t * (s Λ : ℂ)) • unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
  intro E _ _ _ r X g bas idx n hs hn D M _ hM v₀ hv₀
  have one {Λ} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
    obtain ⟨h1, h2, s, h3, -, h4⟩ := h
    exact ⟨h1, h2, s, h3, Nat.coprime_one_right s, h4⟩
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hsh {L} (hL : L ∈ D.lats) : SelfD X (D.sh L) := Lev.selfD_idq D.ne_bot D.proper D.cop hL.1
  have vac := TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have ten := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have pp := GlobalTheory.Dict.ProjProj.proj_proj E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have hΛ₀ : X.Λ ∈ D.lats := ⟨Lev.selfD_of_sympl hs, 1, Lev.cop_one, fun v hv => by simpa using hv,
    fun v hv => by simpa using hv⟩
  have key : ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v →
      ‖SW.ip v (v₀ L)‖ = √((((D.sh X.Λ).toAddSubgroup.relIndex X.Λ.toAddSubgroup ^ n : ℕ) : ℝ)⁻¹) ∧
        0 < ‖SW.ip v (v₀ L)‖ := by
    intro L hL v hv
    have h := (vac L hL.1 1 _ hstd).2.2.2 _ (hsh hL) _ hstd v _ hv (hv₀ L hL)
    rw [((ten L hL.1 1 _ hstd).2.2.2.2.1 _ (hsh hL)).1] at h
    obtain ⟨-, s, h1, h2, h3⟩ := hL
    rw [Level.sh, relIndex_shift h1.of_mul_right_left h2 h3] at h
    exact eq_sqrt (norm_nonneg _) h
  refine ⟨_, fun Λ => √(((Λ.toAddSubgroup.relIndex (stdL E n).toAddSubgroup ^ r : ℕ) : ℝ)⁻¹), ?_,
    fun L hL v hv => ⟨_, (key L hL v hv).1, fun Λ hΛ => ?_⟩⟩
  · obtain ⟨v, hv⟩ := (vac _ hΛ₀.1 1 _ hstd).1
    exact (key _ hΛ₀ v hv).1 ▸ (key _ hΛ₀ v hv).2
  obtain ⟨⟨u, hu⟩, -, hp, -⟩ := vac _ (hsh hL) 1 _ (one hΛ)
  have h := (vac _ (hsh hL) 1 _ hstd).2.2.2 _ (hsh hL) _ (one hΛ) _ u (hv₀ L hL) hu
  rw [(ten _ (hsh hL) 1 _ hstd).2.2.2.2.2 _ (one hΛ)] at h
  obtain ⟨h1, h2⟩ := eq_sqrt (norm_nonneg _) h
  simp only [← h1]
  refine ⟨h2, ?_⟩
  obtain ⟨s, -, hc, s1, s2⟩ := hΛ.2.2
  have hM' : (M : 𝓞 E) ∈ conjI D.𝔪 := Lev.mem_conjI.2 (by rwa [map_natCast])
  have e1 := pp L L _ hL.1 hL.1 (hsh hL) _ hstd _ (one hΛ) _ (one hΛ)
    (le_sup_of_coprime hc (nsmul_tens_left s1) (nsmul_tens_right fun x hx =>
      Lev.smul_le_idq _ _ _ (Submodule.smul_mem_smul hM hx))) v hv
  have e2 := pp L _ _ hL.1 (hsh hL) (hsh hL) _ hstd _ hstd _ (one hΛ)
    (le_sup_of_coprime hc.symm (nsmul_tens_right fun x hx => Submodule.smul_le_right (hx _ hM'))
      (nsmul_tens_left s2)) v hv
  have b₀ := (hv₀ L hL).1
  rw [e1, ← e2, (vac _ (hsh hL) 1 _ hstd).2.2.1 v hv.1 _ (hv₀ L hL), hp _ (TensVac.sb_smul _ b₀) u hu,
    hp _ b₀ u hu, TensVac.ip_smul_left _ b₀ hu.1, mul_smul, mul_smul, ← smul_eq_unitv hu.1 hu.2.1 h2]

end GlobalTheory.Dict.ShVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReflexNormMulConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

noncomputable section

namespace GlobalTheory.BetaChange

open GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.LatticeBetaCompare GlobalTheory.SW.Nbr
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem form_adj (h : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * h.mulVec w j =
      ∑ j, IsCMField.complexConj E ((adjM h).mulVec v j) * w j := by
  simp only [Matrix.mulVec, dotProduct, adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {h : Matrix (Fin n) (Fin n) E} (hu : IsUnitaryM h) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (actLat h Λ).Unimod := by
  have h1 : adjM h * h = 1 := hu
  have h2 : h * adjM h = 1 := mul_eq_one_comm.1 h1
  intro v
  have e : v ∈ (actLat h Λ).La ↔ (adjM h).mulVec v ∈ Λ.La := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (adjM h).mulVec (h.mulVec u) ∈ _
      rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · intro hv
      refine ⟨_, hv, ?_⟩
      change h.mulVec _ = _
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e, hΛ]
  constructor
  · rintro hv _ ⟨u, hu, rfl⟩
    exact (form_adj h v u).symm ▸ hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ⟨w, hw, rfl⟩

variable {H : Host E} (Dw : Datum H) {l : Geo.Tor.Level H} (c : Coeff l)

theorem reflexNorm_mul_conj (g : 𝓞 E) :
    reflexNorm Dw c ((g * co g : 𝓞 E) : E) = ((Ideal.absNorm (Ideal.span {g}) ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  have h := (isBe_principal Dw c g).2 c.F.val.toRingHom
  apply c.F.val.toRingHom.injective
  rw [map_natCast]
  have e : c.F.val.toRingHom (reflexNorm Dw c ((g * co g : 𝓞 E) : E)) =
      c.F.val.toRingHom (reflexNorm Dw c (g : E)) * conj (c.F.val.toRingHom (reflexNorm Dw c (g : E))) := by
    simp only [reflexNorm, map_prod, map_pow, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    congr 1
    change σ ((g : E) * IsCMField.complexConj E (g : E)) = σ g * conj (σ g)
    rw [map_mul, IsCMField.complexEmbedding_complexConj]
  rw [e, Complex.mul_conj', ← Complex.ofReal_pow, h]
  push_cast
  rfl

theorem isBe_mul_conj (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    IsBe Dw c (J * conjI J) ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  let I₀ : (Ideal (𝓞 E))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
  obtain ⟨k, hk, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I₀)).exists_pow_eq_one
  rw [← map_pow] at e
  obtain ⟨g, hg⟩ : (J ^ k).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I₀ ^ k).2).1 e
  change J ^ k = Ideal.span {g} at hg
  refine isBe_of_pow hk ?_
  have e1 : (J * conjI J) ^ k = Ideal.span {g * co g} := by
    rw [mul_pow, conjI_eq, ← Ideal.map_pow, hg, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  have e2 : ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) ^ k = reflexNorm Dw c ((g * co g : 𝓞 E) : E) := by
    rw [reflexNorm_mul_conj, ← hg, map_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e1, e2]
  exact isBe_principal Dw c _

theorem isBe_of_isBeta {Λ : GenLat E n} (hΛ : Λ.Unimod) {b : c.F} (hb : IsBeta Dw c Λ b) {J : Ideal (𝓞 E)}
    (hN : Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index)
    (hJ : detSpan Λ.Ln = J • detSpan Λ.La) : IsBe Dw c J b := by
  have hu0 : IsUnit (detSpan Λ.La) :=
    isUnit_detSpan (GenusLatCompare.latEquiv.symm ⟨Λ, GenusLatCompare.isLat_of_unimod Λ hΛ⟩)
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ) :=
    IsUnit.prod_iff.2 fun τ _ => by rw [idealAt_eq]; exact (hu0.map _).pow _
  obtain ⟨-, h1, h2⟩ := hb
  refine ⟨?_, fun s => by rw [hN]; exact h2 s⟩
  have e : ∀ τ, idealAt c Λ.Ln τ =
      coeI c.F (J.map (RingOfIntegers.mapRingHom (embF c τ))) * idealAt c Λ.La τ := fun τ => by
    rw [idealAt_eq, idealAt_eq, hJ, smul_eq_coeI_mul, map_mul, extend_coeI]
  rw [← span_eq_coeI_iff, coeI_reflexIdeal]
  rw [BetaIs] at h1
  simp only [e, mul_pow, Finset.prod_mul_distrib] at h1
  exact hu.mul_left_inj.1 h1

omit [IsCMField E] in
theorem map_mulLeft_eq (x : E) (M : Submodule (𝓞 E) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 E) x) M = Submodule.span (𝓞 E) {x} * M := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  rfl

omit [IsCMField E] in
theorem coeI_span (u : 𝓞 E) : coeI E (Ideal.span {u}) = Submodule.span (𝓞 E) {(u : E)} :=
  IsLocalization.coeSubmodule_span_singleton E u

theorem beta_sq_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F), Λ.Unimod → IsUnitaryM h → IsBeta Dw c Λ b → IsBeta Dw c (actLat h Λ) b' → ∃ m : ℕ, 0 < m ∧ (b ^ 2 * ((((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F)) ^ m = (b' ^ 2 * ((((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F) * ∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) ^ m := by
  intro E _ _ _ H Dw l c n Λ h b b' hΛ hu hb hb'
  have hΛ' := unimod_act hu hΛ
  obtain ⟨J, hJ0, hN, hJ1, hJ2, hdet⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n Λ hΛ
  obtain ⟨J', hJ0', hN', hJ1', hJ2', -⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n _ hΛ'
  have hB := isBe_of_isBeta Dw c hΛ hb hN hJ1
  have hB' := isBe_of_isBeta Dw c hΛ' hb' hN' hJ1'
  obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := 𝓞 E) h.det
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hvE : (v : E) ≠ 0 := by simpa using hv0
  have huv' : (u : E) = h.det * (v : E) := by
    rw [← huv]; exact (div_mul_cancel₀ _ hvE).symm
  have k1 : coeI E (conjI J) = coeI E J * detSpan Λ.La := by
    rw [← smul_eq_coeI_mul]; exact hJ2.symm.trans hJ1
  have k2 : coeI E (conjI J') = coeI E J' * (Submodule.span (𝓞 E) {h.det} * detSpan Λ.La) := by
    rw [← smul_eq_coeI_mul, ← map_mulLeft_eq]
    exact (hJ2'.symm.trans hJ1').trans (by rw [hdet]; rfl)
  have key : conjI J' * J * Ideal.span {v} = conjI J * J' * Ideal.span {u} := by
    apply IsFractionRing.coeSubmodule_injective (𝓞 E) E
    change coeI E _ = coeI E _
    simp only [map_mul, k1, k2, coeI_span]
    rw [huv', ← Set.singleton_mul_singleton, ← Submodule.span_mul_span]
    ring
  have a1 := isBe_mul (isBe_mul (isBe_pow hB 2) (isBe_mul_conj Dw c J' hJ0')) (isBe_principal Dw c v)
  have a2 := isBe_mul (isBe_mul (isBe_pow hB' 2) (isBe_mul_conj Dw c J hJ0)) (isBe_principal Dw c u)
  have e : J' ^ 2 * (J * conjI J) * Ideal.span {u} = J ^ 2 * (J' * conjI J') * Ideal.span {v} := by
    calc _ = J * J' * (conjI J * J' * Ideal.span {u}) := by ring
      _ = _ := by rw [← key]; ring
  rw [e] at a2
  have hc : conjI J' ≠ ⊥ := fun h0 => hJ0' (by
    rw [← conjI_conjI J', h0, conjI_eq, Ideal.map_bot])
  have hs : Ideal.span {v} ≠ (⊥ : Ideal (𝓞 E)) := by simpa using hv0
  obtain ⟨z, hz, ez⟩ := isBe_unique
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ0) (mul_ne_zero hJ0' hc)) hs) a2 a1
  obtain ⟨m, hm, hzm⟩ := hz.exists_pow_eq_one
  have hψ : reflexNorm Dw c (v : E) ≠ 0 := isBe_ne_zero hs (isBe_principal Dw c v)
  have hψu : reflexNorm Dw c (u : E) = (∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) * reflexNorm Dw c (v : E) := by
    simp only [huv', reflexNorm, map_mul, mul_pow, Finset.prod_mul_distrib]
  rw [hψu, ← _root_.mul_assoc, ← _root_.mul_assoc, hN, hN'] at ez
  have ez' := mul_right_cancel₀ hψ ez
  refine ⟨m, hm, ?_⟩
  rw [ez', _root_.mul_assoc z, mul_pow z, hzm, _root_.one_mul]

end GlobalTheory.BetaChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDefiniteHermitianOfFourMulLtStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_definiteHermitian_of_four_mul_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  first | exact @GlobalTheory.SW.siegel_weil_definite | exact GlobalTheory.SW.siegel_weil_definite | (intros; apply GlobalTheory.SW.siegel_weil_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_sum_left (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hx X bas idx x (∑ k, z k) w = ∑ k, hx X bas idx x (z k) w := by
  unfold hx
  rw [Matrix.mulVec_sum, sum_dotProduct]

theorem hx_sum_right (x : Frame X.Ψ r) (z : Fin g → ℂ) (w : Fin n → Fin g → ℂ) :
    hx X bas idx x z (∑ k, w k) = ∑ k, hx X bas idx x z (w k) := by
  unfold hx
  rw [Matrix.mulVec_sum, star_sum, Matrix.mulVec_sum, dotProduct_sum]

theorem hAct_eq_sum (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h z k = ∑ a, fun j => rowType X (idx j) (h k a) * z a j := by
  funext j
  rw [Finset.sum_apply]
  rfl

theorem hAct_add_smul (h : Matrix (Fin n) (Fin n) E) (z w : Fin n → Fin g → ℂ) (c : ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h (fun a => z a + c • w a) k =
      GlobalTheory.Dict.hAct X idx h z k + c • GlobalTheory.Dict.hAct X idx h w k := by
  funext j
  simp only [GlobalTheory.Dict.hAct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem sum_hx_hAct (x : Frame X.Ψ r)
    (hadj : ∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w =
      hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j))
    (h : Matrix (Fin n) (Fin n) E) (hh : ccT h * h = 1) (z w : Fin n → Fin g → ℂ) :
    ∑ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ k, hx X bas idx x (z k) (w k) := by

  have key : ∀ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ a, ∑ b, hx X bas idx x (z a) (fun j => rowType X (idx j) (cc (h k a) * h k b) * w b j) := by
    intro k
    rw [hAct_eq_sum, hAct_eq_sum, hx_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj]
    congr 1
    funext j
    rw [map_mul, _root_.mul_assoc]

  have hcol : ∀ a b, ∑ k, cc (h k a) * h k b = (1 : Matrix (Fin n) (Fin n) E) a b := by
    intro a b
    rw [← hh, Matrix.mul_apply]
    rfl
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp only [← hx_sum_right]
  congr 1
  funext j
  simp only [Finset.sum_apply]
  have hj : ∀ b, ∑ k, rowType X (idx j) (cc (h k a) * h k b) * w b j =
      rowType X (idx j) ((1 : Matrix (Fin n) (Fin n) E) a b) * w b j := by
    intro b
    rw [← Finset.sum_mul, ← map_sum, hcol]
  simp only [hj, Matrix.one_apply, apply_ite, map_one, map_zero, ite_mul, _root_.one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem pv_mul_row (x : Frame X.Ψ r)
    (hsm : ∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j)
    (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E) (k : Fin n) :
    pv X idx x ((h * y) k) = GlobalTheory.Dict.hAct X idx h (fun a => pv X idx x (y a)) k := by
  have hrow : (h * y) k = ∑ a, h k a • y a := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply]

  have hadd : pv X idx x (∑ a, h k a • y a) = ∑ a, pv X idx x (h k a • y a) := by
    funext j
    rw [Finset.sum_apply]
    exact (congrFun (map_sum (perLin X x) (fun a => h k a • y a) Finset.univ) (idx j)).trans
      (Finset.sum_apply _ _ _)
  rw [hrow, hadd, hAct_eq_sum]
  exact Finset.sum_congr rfl fun a _ => hsm (h k a) (y a)

end GlobalTheory.Dict.ColHeis

open GlobalTheory.Dict.ColHeis in

theorem GlobalTheory.Dict.thA_heisG_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hS hn h hh φ φ' hφ hφ' t x hxd hrel y z
  obtain ⟨-, -, -, hadj, hsm, -⟩ := GlobalTheory.T.hermitianFormAtFrame_laws E r X g bas idx n hS hn x hxd
  have HL := (heisG_laws E r X g bas idx n hS hn).2.2.2
  rw [((HL (h * y) φ' hφ').2.2.2.2) x hxd (hAct X idx h z), ((HL y φ hφ).2.2.2.2) x hxd z]

  have hP : ∀ k, per X x ((h * y) k) ∘ idx = hAct X idx h (fun a => pv X idx x (y a)) k :=
    fun k => pv_mul_row X idx x hsm h y k
  simp only [hP]

  have hT : thA X bas idx φ' x (fun k => hAct X idx h z k + hAct X idx h (fun a => pv X idx x (y a)) k) =
      t * thA X bas idx φ x (fun k => z k + per X x (y k) ∘ idx) := by
    refine Eq.trans ?_ (hrel (fun k => z k + pv X idx x (y k)))
    congr 1
    funext k
    simpa using (hAct_add_smul X idx h z (fun a => pv X idx x (y a)) 1 k).symm
  rw [hT, mul_left_comm]
  refine congrArg (t * ·) (congrArg (· * _) (congrArg cexp (congrArg (fun s : ℂ => -((Real.pi : ℂ) * s)) ?_)))

  have hE : ∀ k, hAct X idx h z k + (1 / 2 : ℂ) • hAct X idx h (fun a => pv X idx x (y a)) k =
      hAct X idx h (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a)) k :=
    fun k => (hAct_add_smul X idx h z _ _ k).symm
  simp only [hE]
  exact sum_hx_hAct X bas idx x hadj h hh (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a))
    (fun a => pv X idx x (y a))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierUnitaryCocycleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_multiplier_unitary_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : SW.Level X, ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1) ∧ (∀ L ∈ D.lats, mu 1 L = 1) ∧ ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
  first | exact @GlobalTheory.Dict.vac_multiplier_cocycle | exact GlobalTheory.Dict.vac_multiplier_cocycle | (intros; apply GlobalTheory.Dict.vac_multiplier_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumTensorLatticeFixedRationalHeisenbergStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas w (tens Λ L) v → ∃ A ε, VacS A ε v := by
  first | exact @GlobalTheory.Phase.vacS_of_isVac | exact GlobalTheory.Phase.vacS_of_isVac | (intros; apply GlobalTheory.Phase.vacS_of_isVac <;> assumption)
end

