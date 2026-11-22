import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqNormSumRepsMulIndexLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NcardImageOfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFamiliesCongrModUnitriangular
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoweringDifferenceOfIsometries
section
open Matrix

namespace GlobalTheory

theorem hform_sub_left_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x x' y : n → A) :
    Formalism.UG.hform σ J (x - x') y = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem hform_eq_dotProduct_mulVec {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_eq_of_unitary {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J γ : Matrix (Fin n) (Fin n) K) (hγ : Formalism.UG.cT σ γ * J * γ = J) (x y : Fin n → K) :
    Formalism.UG.hform σ J (γ *ᵥ x) (γ *ᵥ y) = Formalism.UG.hform σ J x y := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  have h1 : (fun i => σ ((γ *ᵥ x) i)) = γ.map σ *ᵥ (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ γ x i
  unfold Formalism.UG.cT at hγ
  rw [Matrix.mul_assoc] at hγ
  rw [h1, ← vecMul_transpose (γ.map σ), ← dotProduct_mulVec]
  simp only [mulVec_mulVec, hγ]

theorem lowering_difference_of_isometries :
    ∀ (K R : Type) [Field K] [StarRing K] [CommRing R] [Algebra R K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm (starRingEnd K) J → ∀ (a : ℕ) (G : ℕ → Submodule R (Fin n → K)), G 0 = ⊥ → Monotone G → (∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, Formalism.UG.hform (starRingEnd K) J s y = 0) → ∀ γ γ' : Matrix (Fin n) (Fin n) K, Formalism.UG.cT (starRingEnd K) γ * J * γ = J → Formalism.UG.cT (starRingEnd K) γ' * J * γ' = J → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ - 1) *ᵥ y ∈ G p) → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ' - 1) *ᵥ y ∈ G p) → ∀ c : ℕ, 1 ≤ c → (∀ q p : ℕ, q < p → q + p ≤ 2 * a → p - q < c → ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G q) → (∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c)) ∧ ∀ p p' : ℕ, p ≤ 2 * a → p' ≤ 2 * a → p + p' ≤ 2 * a + c → ∀ x ∈ G (p + 1), ∀ y ∈ G (p' + 1), Formalism.UG.hform (starRingEnd K) J ((γ - γ') *ᵥ x) y + Formalism.UG.hform (starRingEnd K) J x ((γ - γ') *ᵥ y) = 0 := by
  intro K R _ _ _ _ n J _ a G hG0 hGm hdual γ γ' hγ hγ' hl hl' c hc hlow
  set hf := Formalism.UG.hform (starRingEnd K) J with hhf
  have hL : ∀ x x' y, hf (x - x') y = hf x y - hf x' y := fun x x' y => hform_sub_left_flag _ J x x' y
  have hR : ∀ x y y', hf x (y - y') = hf x y - hf x y' := fun x y y' => hform_sub_right_flag _ J x y y'
  have iso : ∀ x y, hf (γ *ᵥ x) (γ *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ hγ
  have iso' : ∀ x y, hf (γ' *ᵥ x) (γ' *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ' hγ'
  have h0 : ∀ v, hf 0 v = 0 := fun v => by simp [hhf, Formalism.UG.hform]
  have mem0 : ∀ y ∈ G 0, y = 0 := fun y hy => by
    rw [hG0] at hy
    exact (Submodule.mem_bot R).1 hy
  have orth : ∀ m m', m + m' ≤ 2 * a + 1 → ∀ u ∈ G m, ∀ v ∈ G m', hf u v = 0 := by
    intro m m' hmm u hu v hv
    exact ((hdual m (by omega) v).1 (hGm (by omega) hv)).2 u hu
  have key : ∀ x y, hf ((γ - γ') *ᵥ x) (γ *ᵥ y) + hf (γ' *ᵥ x) ((γ - γ') *ᵥ y) = 0 := by
    intro x y
    rw [sub_mulVec, sub_mulVec, hL, hR, iso, iso']
    ring
  have base : ∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - 1) := by
    intro p hp y hy
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [mem0 y hy, mulVec_zero]
      exact zero_mem _
    · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
      have e : (γ - γ') *ᵥ y = (γ - 1) *ᵥ y - (γ' - 1) *ᵥ y := by
        simp only [sub_mulVec, one_mulVec]
        abel
      rw [e, Nat.add_sub_cancel]
      exact sub_mem (hl p0 (by omega) y hy) (hl' p0 (by omega) y hy)
  have main1 : ∀ p, p ≤ 2 * a + 1 → ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp y hy
      by_cases hA : c = 1 ∨ p ≤ 1
      · exact hGm (by omega) (base p hp y hy)
      by_cases hB : 2 * p ≤ 2 * a + 1 + c ∨ p < c
      · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
        exact hlow (p0 + 1 - c) p0 (by omega) (by omega) (by omega) y hy
      have hγy : γ *ᵥ y ∈ G p := by
        have e1 : γ *ᵥ y = (γ - 1) *ᵥ y + y := by
          simp only [sub_mulVec, one_mulVec]
          abel
        rw [e1]
        refine add_mem (hGm (Nat.sub_le p 1) (hl (p - 1) (by omega) y ?_)) hy
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      have inner : ∀ j, j ≤ 2 * a + 1 - (p - c) → ∀ s ∈ G j, hf s ((γ - γ') *ᵥ y) = 0 := by
        intro j
        induction j with
        | zero =>
          intro _ s hs
          rw [mem0 s hs, h0]
        | succ j ihj =>
          intro hj s hs
          have k := key s y
          have ha : hf ((γ' - 1) *ᵥ s) ((γ - γ') *ᵥ y) =
              hf (γ' *ᵥ s) ((γ - γ') *ᵥ y) - hf s ((γ - γ') *ᵥ y) := by
            rw [sub_mulVec γ' 1, one_mulVec, hL]
          have hz1 := ihj (by omega) _ (hl' j (by omega) s hs)
          have hz2 := orth (j + 1 - c) p (by omega) _ (ih (j + 1) (by omega) (by omega) s hs) _ hγy
          linear_combination k + ha - hz1 - hz2
      have hd := (hdual (2 * a + 1 - (p - c)) (by omega) ((γ - γ') *ᵥ y)).2
        ⟨hGm (by omega) (base p hp y hy), fun s hs => inner _ le_rfl s hs⟩
      have e2 : 2 * a + 1 - (2 * a + 1 - (p - c)) = p - c := by omega
      rwa [e2] at hd
  refine ⟨main1, ?_⟩
  intro p p' hp hp' hpp x hx y hy
  have e3 : hf ((γ - γ') *ᵥ x) ((γ - 1) *ᵥ y) = 0 :=
    orth (p + 1 - c) p' (by omega) _ (main1 (p + 1) (by omega) x hx) _ (hl p' hp' y hy)
  have e4 : hf ((γ' - 1) *ᵥ x) ((γ - γ') *ᵥ y) = 0 :=
    orth p (p' + 1 - c) (by omega) _ (hl' p hp x hx) _ (main1 (p' + 1) (by omega) y hy)
  rw [sub_mulVec γ 1, one_mulVec, hR] at e3
  rw [sub_mulVec γ' 1, one_mulVec, hL] at e4
  linear_combination key x y - e3 - e4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} in

theorem _root_.GlobalTheory.HL.Glue.mem_span_single_iff {R : Type} [CommRing R] (O : Subring R) (n : ℕ)
    (v : Fin n → R) :
    v ∈ Submodule.span O (Set.range fun i => (Pi.single i 1 : Fin n → R)) ↔ ∀ i, v i ∈ O := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      intro i
      by_cases h : i = j
      · subst h; simp [O.one_mem]
      · simp [Pi.single_apply, h, O.zero_mem]
    | zero => intro i; simpa using O.zero_mem
    | add a b _ _ ha hb => intro i; simpa using O.add_mem (ha i) (hb i)
    | smul c a _ ha => intro i; simpa [Subring.smul_def] using O.mul_mem c.2 (ha i)
  · intro hv
    have hsum : v = ∑ i, (⟨v i, hv i⟩ : O) • (Pi.single i 1 : Fin n → R) := by
      ext j
      simp [Subring.smul_def, Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} in

theorem _root_.GlobalTheory.HL.Glue.ιE_mem (A : _root_.GlobalTheory.HL.Places F E sig)
    (p : HeightOneSpectrum (𝓞 F)) (x : E) (hx : IsIntegral ℤ x) :
    (A.loc p).ιE x ∈ (A.L p).O := by
  rw [_root_.Formalism.MainNotions.S.Loc.LocE.O_def]
  exact (hx.map (A.loc p).ιE.toIntAlgHom).tower_top

end GlobalTheory.HL.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSummand

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_left (x y z : Fin n → E) : hf L Hm (x + y) z = hf L Hm x z + hf L Hm y z := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin n → E) : hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : E) (x z : Fin n → E) : hf L Hm (c • x) z = c * hf L Hm x z := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : E) (x z : Fin n → E) : hf L Hm x (c • z) = L.cj c * hf L Hm x z := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hf_zero_left (z : Fin n → E) : hf L Hm 0 z = 0 := by
  simp [hf]

theorem hf_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → E) (z : Fin n → E) :
    hf L Hm (∑ a ∈ s, x a) z = ∑ a ∈ s, hf L Hm (x a) z := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, ih]

theorem cj_hf (h : IsHerm L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end

theorem norm_gauss_sum_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (i N : ℕ), 1 ≤ i → i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ∀ (χ : AddChar (Fin n → E) ℂ), (∀ u, ‖χ u‖ = 1) → (∀ u ∈ UU, χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ‖∑ u ∈ R, ψ (t * nrm u) * χ u‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * ρ : ℤ)) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH ϖ hϖ ψ hψ1 hψ UU hUU d e heU hee i N _ hiN t u₀ ht χ hχ1 hχ
    R nrm hnrm hRO hR
  obtain ⟨-, -, hdual, -, hint, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hO : ∀ c : 𝒪[F], algebraMap F E c ∈ L.O := fun c => (hint c).2 c.2
  have hsm : ∀ c ∈ L.O, ∀ x ∈ UU, c • x ∈ UU := fun c hc x hx =>
    UU.smul_mem (⟨c, hc⟩ : L.O) hx
  let I : ℕ → Ideal L.O := fun j => Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
  have hI : ∀ j (x : L.O), x ∈ I j ↔ ∃ c ∈ L.O, (x : E) = algebraMap F E ((ϖ : F) ^ j) * c := by
    intro j x
    have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
        = {⟨algebraMap F E ((ϖ : F) ^ j), hO (ϖ ^ j)⟩} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    simp only [I]
    rw [hset, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
  let P₀ : AddSubgroup (Fin d → L.O) := AddSubgroup.pi Set.univ fun _ => (I i).toAddSubgroup
  have hP₀ : ∀ x, x ∈ P₀ ↔ ∀ a, ∃ c ∈ L.O, (x a : E) = algebraMap F E ((ϖ : F) ^ i) * c := by
    intro x
    simp only [P₀, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, hI]
  have hidx₀ : P₀.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    have : (I i).toAddSubgroup.index = resQ ϖ ^ (2 * i) := hcard i
    simp only [P₀]
    rw [AddSubgroup.index_pi, Finset.prod_const, this, Finset.card_univ, Fintype.card_fin]
    ring
  let φ : UU →+ (Fin d → L.O) :=
    { toFun := fun m a => ⟨hf L Hm m (e a), hUU _ m.2 _ (heU a)⟩
      map_zero' := funext fun a => Subtype.ext (hf_zero_left L Hm _)
      map_add' := fun x y => funext fun a => Subtype.ext (hf_add_left L Hm _ _ _) }
  have hφ : Function.Surjective φ := fun c => by
    refine ⟨⟨∑ b, (c b : E) • e b, UU.sum_mem fun b _ => hsm _ (c b).2 _ (heU b)⟩,
      funext fun a => Subtype.ext ?_⟩
    show hf L Hm (∑ b, (c b : E) • e b) (e a) = c a
    simp [hf_sum_left, hf_smul_left, hee]
  let Q : AddSubgroup UU := P₀.comap φ
  have hQ : ∀ x : UU, x ∈ Q ↔
      ∀ a, ∃ c ∈ L.O, hf L Hm x (e a) = algebraMap F E ((ϖ : F) ^ i) * c := fun x => hP₀ (φ x)
  have hidx : Q.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    rw [← hidx₀]; exact AddSubgroup.index_comap_of_surjective P₀ hφ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hiN
  let P : AddSubgroup UU :=
    { carrier := {x | ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y}
      zero_mem' := ⟨0, UU.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨x', hx', hx⟩ ⟨y', hy', hy⟩
        exact ⟨x' + y', UU.add_mem hx' hy', by rw [Submodule.coe_add, hx, hy, smul_add]⟩
      neg_mem' := by
        rintro x ⟨x', hx', hx⟩
        exact ⟨-x', UU.neg_mem hx', by rw [Submodule.coe_neg, hx, smul_neg]⟩ }
  have hP : ∀ x : UU, x ∈ P ↔
      ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y := fun _ => Iff.rfl
  have hPQ : P ≤ Q := fun x hx => (hQ x).2 fun a => by
    obtain ⟨y, hy, h⟩ := (hP x).1 hx
    refine ⟨algebraMap F E ((ϖ : F) ^ k) * hf L Hm y (e a),
      L.O.mul_mem (hO (ϖ ^ k)) (hUU _ hy _ (heU a)), ?_⟩
    rw [h, hf_smul_left, pow_add, map_mul, mul_assoc]
  have hιinj : Function.Injective (Subtype.val : UU → Fin n → E) := Subtype.val_injective
  have hrange : ∀ u ∈ R, u ∈ Set.range (Subtype.val : UU → Fin n → E) :=
    fun u hu => ⟨⟨u, hRO u hu⟩, rfl⟩
  let R' := R.preimage (Subtype.val : UU → Fin n → E) hιinj.injOn
  have hτ : algebraMap F E t * algebraMap F E ((ϖ : F) ^ i)
      = algebraMap F E ((u₀ : 𝒪[F]) : F) := by rw [← map_mul, ht]
  have key := GaussSum.sq_norm_sum_reps_mul_index_le P Q hPQ R' ?_
    (fun m => ψ (t * nrm m) * χ m) (fun m => by rw [norm_mul, hψ1, hχ1, mul_one]) ?_ ?_
  · rw [Finset.sum_preimage Subtype.val R hιinj.injOn (fun u => ψ (t * nrm u) * χ u)
      (fun u hu h => (h (hrange u hu)).elim), Finset.card_preimage, hidx,
      Finset.filter_true_of_mem hrange, Nat.cast_pow, ← mul_pow] at key
    have hq0 : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
    have h := (sq_le_sq₀ (by positivity) (by positivity)).1 key
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact_mod_cast h
  · intro u
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR u u.2
    obtain ⟨w, rfl⟩ := hrange w hw
    refine ⟨w, ⟨Finset.mem_preimage.2 hw, (hP _).2 hw'⟩, fun y hy => hιinj ?_⟩
    exact huniq _ ⟨Finset.mem_preimage.1 hy.1, (hP _).1 hy.2⟩
  · intro u p hp
    obtain ⟨c, hc, hpc⟩ := (hP p).1 hp
    have h1 : χ p = 1 := by rw [hpc, hχ c hc]
    have h3 : t * (nrm (u + p) - nrm u) ∈ 𝒪[F] := by
      rw [← hint, map_mul, map_sub, hnrm, hnrm]
      have : algebraMap F E t * (hf L Hm (u + p) (u + p) - hf L Hm u u)
          = algebraMap F E ((u₀ : 𝒪[F]) : F) * algebraMap F E ((ϖ : F) ^ k)
            * (hf L Hm c (u + p) + hf L Hm u c) := by
        have e1 : hf L Hm p (u + p) = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm c (u + p) := by
          rw [← hf_smul_left, ← hpc]
        have e2 : hf L Hm u p = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm u c := by
          rw [hpc, hf_smul_right, AlgEquiv.commutes]
        rw [hf_add_left, e1, hf_add_right L Hm u u p, e2, ← hτ, pow_add, map_mul]
        ring
      rw [this]
      exact L.O.mul_mem (L.O.mul_mem (hO _) (hO (ϖ ^ k)))
        (L.O.add_mem (hUU _ hc _ (UU.add_mem u.2 p.2)) (hUU _ u.2 _ hc))
    have h4 := (hψ _).2 h3 1
    have h5 : t * nrm (u + p) = t * nrm u
        + t * (nrm (u + p) - nrm u) * ((1 : 𝒪[F]) : F) := by
      push_cast; ring
    show ψ (t * nrm (u + p)) * χ (u + p) = _
    rw [h5, AddChar.map_add_eq_mul, h4, mul_one, AddChar.map_add_eq_mul, h1, mul_one]
  · intro h hh
    obtain ⟨a, ha⟩ := not_forall.1 fun h' => hh ((hQ h).2 h')
    obtain ⟨z, hz⟩ : ∃ z, z = hf L Hm h (e a) := ⟨_, rfl⟩
    rw [← hz] at ha
    have h1 : algebraMap F E t * z ∉ L.O := fun h' => ha
      ⟨algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (algebraMap F E t * z),
        L.O.mul_mem (hO _) h', by
          have h2 : algebraMap F E ((u₀ : 𝒪[F]) : F)
              * algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
            rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
          linear_combination (-z) * h2
            - algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * z * hτ⟩
    obtain ⟨b, hb⟩ := not_forall.1 fun h' => h1 (hdual _ h')
    obtain ⟨hb, hb'⟩ := Classical.not_imp.1 hb
    obtain ⟨s, hs⟩ := (L.cj_fix (algebraMap F E t * z * L.cj b
      + L.cj (algebraMap F E t * z * L.cj b))).1 (by rw [map_add, L.cj_cj, add_comm])
    have hs' : s ∉ 𝒪[F] := fun h' => hb' ⟨⟨s, h'⟩, hs.symm⟩
    obtain ⟨y, hy⟩ := not_forall.1 fun h' => hs' ((hψ s).1 h')
    let v : UU := ⟨(algebraMap F E y * b) • e a, hsm _ (L.O.mul_mem (hO y) hb) _ (heU a)⟩
    refine ⟨v, ψ (s * y), hy, fun u => ?_⟩
    have h2 : t * nrm (u + v + h) - t * nrm (u + v)
        = s * y + (t * nrm (u + h) - t * nrm u) := by
      apply hinj
      have h3 : hf L Hm v h = algebraMap F E y * b * L.cj z := by
        rw [hz, cj_hf L Hm hH.1]
        exact hf_smul_left L Hm _ _ _
      have h3' : hf L Hm h v = algebraMap F E y * L.cj b * z := by
        rw [← cj_hf L Hm hH.1, h3]
        simp only [map_mul, AlgEquiv.commutes, L.cj_cj]
      simp only [map_mul, AlgEquiv.commutes, L.cj_cj] at hs
      simp only [map_sub, map_add (algebraMap F E), map_mul, hnrm, hs, hf_add_left, hf_add_right,
        h3, h3']
      ring
    have h4 : (u : Fin n → E) + v + h - (u + v) = u + h - u := by abel
    simp only [map_mul, Submodule.coe_add]
    rw [mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1,
      mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1, h2, h4,
      AddChar.map_add_eq_mul, mul_assoc]

end GlobalTheory.HL.GaussSummand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImage
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem relIndex_pair_comap_of_dense_image : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  intro Γ G _ _ φ K U h
  refine ⟨relIndex_comap_of_dense_image φ K U fun g hg => h g (Or.inr hg), ?_⟩
  refine relIndex_comap_of_dense_image φ U K fun g hg => ?_
  obtain ⟨γ, hγ⟩ := h g (Or.inl hg)
  exact ⟨γ, by rwa [inf_comm]⟩

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelVolMul
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContAut

theorem relVol_mul {W : Type} [AddCommGroup W] {X Y B : AddSubgroup W}
    (hYX : Y.relIndex X ≠ 0) (hBY : B.relIndex Y ≠ 0) :
    relVol X B = relVol X Y * relVol Y B := by
  have hCY : (B ⊓ Y).relIndex Y ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have hCX : (B ⊓ Y).relIndex X ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCY hYX
  have e1 := ContModel.relVol_of_le (W0 := X) (inf_le_left : B ⊓ Y ≤ B) hCX
  have e2 := ContModel.relVol_of_le (W0 := X) (inf_le_right : B ⊓ Y ≤ Y) hCX
  have e3 := ContModel.relVol_of_le (W0 := Y) (inf_le_left : B ⊓ Y ≤ B) hCY
  have e4 : relVol Y (B ⊓ Y) = 1 / ((B ⊓ Y).relIndex Y : ℝ) := by
    unfold relVol
    rw [AddSubgroup.relIndex_eq_one.2 (inf_le_right : B ⊓ Y ≤ Y)]
    simp
  have c : ((B ⊓ Y).relIndex Y : ℝ) ≠ 0 := by exact_mod_cast hCY
  rw [e1, e2, e3, e4]
  field_simp

theorem image_mk {W : Type} [AddCommGroup W] (A : AddSubgroup W) (φ : W ≃+ W) (S : Set W) :
    ∃ f : W ⧸ A → W ⧸ A.map φ.toAddMonoidHom, Function.Injective f ∧
      (QuotientAddGroup.mk : W → W ⧸ A.map φ.toAddMonoidHom) '' (φ '' S)
        = f '' ((QuotientAddGroup.mk : W → W ⧸ A) '' S) := by
  refine ⟨QuotientAddGroup.map A (A.map φ.toAddMonoidHom) φ.toAddMonoidHom
    (AddSubgroup.le_comap_map _ _), ?_, ?_⟩
  · intro u v
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
    intro h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq] at h
    obtain ⟨a, ha, hh⟩ := h
    rw [QuotientAddGroup.eq]
    have : a = -x + y := φ.injective (by simpa using hh)
    rwa [← this]
  · rw [Set.image_image, Set.image_image]
    rfl

theorem cont_image : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (φ : W ≃+ W), (W0.map φ.toAddMonoidHom).relIndex W0 ≠ 0 → W0.relIndex (W0.map φ.toAddMonoidHom) ≠ 0 → ∀ S, IsCO W0 S → IsCO W0 (φ '' S) ∧ cont W0 (φ '' S) = relVol W0 (W0.map φ.toAddMonoidHom) * cont W0 S := by
  intro W _ W0 φ h1 h2 S ⟨A, hA⟩
  have hi : Function.Injective φ.toAddMonoidHom := φ.injective
  have m1 := AddSubgroup.relIndex_map_map_of_injective A W0 hi
  have m2 := AddSubgroup.relIndex_map_map_of_injective W0 A hi
  obtain ⟨f, hf, him⟩ := image_mk A φ S
  have a1 : (A.map φ.toAddMonoidHom).relIndex (W0.map φ.toAddMonoidHom) ≠ 0 := m1 ▸ hA.1
  have a2 : (W0.map φ.toAddMonoidHom).relIndex (A.map φ.toAddMonoidHom) ≠ 0 := m2 ▸ hA.2.1
  have hG : GoodSub W0 (A.map φ.toAddMonoidHom) (φ '' S) := by
    refine ⟨AddSubgroup.relIndex_ne_zero_trans a1 h1, AddSubgroup.relIndex_ne_zero_trans h2 a2,
      ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨x + a, hA.2.2.1 x hx a ha, by simp⟩
    · rw [him]; exact hA.2.2.2.image f
  refine ⟨⟨_, hG⟩, ?_⟩
  rw [ContModel.cont_eq hG, ContModel.cont_eq hA, him, Set.ncard_image_of_injective _ hf,
    relVol_mul h1 a1]
  have : relVol (W0.map φ.toAddMonoidHom) (A.map φ.toAddMonoidHom) = relVol W0 A := by
    unfold relVol; rw [m1, m2]
  rw [this]; ring

end GlobalTheory.HL.ContAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuationStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_lattice_volume_of_det_valuation : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {W : Type} [AddCommGroup W] [Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (φ : W ≃ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ), LinearMap.det (φ : W →ₗ[F] W) = (ϖ : F) ^ a * ((u : 𝒪[F]) : F) → ∀ W0 : AddSubgroup W, (∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) → (W0.map φ.toAddEquiv.toAddMonoidHom).relIndex W0 ≠ 0 ∧ W0.relIndex (W0.map φ.toAddEquiv.toAddMonoidHom) ≠ 0 ∧ relVol W0 (W0.map φ.toAddEquiv.toAddMonoidHom) = (resQ ϖ : ℝ) ^ (-a) := by
  first | exact @GlobalTheory.HL.LatDet.relVol_map | exact GlobalTheory.HL.LatDet.relVol_map | (intros; apply GlobalTheory.HL.LatDet.relVol_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFamiliesCongrModUnitriangularStatement
section
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_families_congr_mod_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) {r : ℕ} (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r) (sg : Loc.SplitG M.L), M.split = some sg → LocNG.IsTermOver P d τ → ∀ (y x : Fin (r + 1) → V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = B a a) → (∀ a, B a a ∈ M.L.O ∧ ∃ t ∈ M.L.O, t * B a a = 1) → (∀ b, y b = ∑ a, B a b • P.A.f a) → (∀ b, x b = ∑ a, B' a b • P.B.f a) → (∀ a, y a ∈ τ.abelian₂) → (∀ b, x b ∈ τ.abelian₂) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ M.L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, x b - ∑ a, ξ a b • y a ∈ H.smulLat (algebraMap F E (sg.q : F)) τ.abelian₂ := by
  first | exact @GlobalTheory.loc_cong_unitri | exact GlobalTheory.loc_cong_unitri | (intros; apply GlobalTheory.loc_cong_unitri <;> assumption)
end

