import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Formalism.PieriBlockIdeals.PieriColumnMinors.DepthNonnegative
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProduct
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush.LowMul

variable {K : Type} [Field K] {n : ℕ}

def Lo (L : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → L i j = 0

def AL (E : Fin n → Fin n → Prop) (C : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → ¬ E i j → C i j = 0

theorem al_mul {E : Fin n → Fin n → Prop} (hE : ∀ i j k, E k j → k ≤ i → i < j → E i j)
    {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C) : AL E (L * C) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hL i k h, zero_mul]
  · rw [hC k j (lt_of_le_of_lt h hij) (fun he => hn (hE i j k he h hij)), mul_zero]

theorem mul_al {E : Fin n → Fin n → Prop} (hE : ∀ i j l, E i l → j ≤ l → i < j → E i j)
    {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R) : AL E (C * R) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l j with h | h
  · rw [hR l j h, mul_zero]
  · rw [hC i l (lt_of_lt_of_le hij h) (fun he => hn (hE i j l he h hij)), zero_mul]

theorem diag_mul {E : Fin n → Fin n → Prop} {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C)
    (x : Fin n) (hx : ∀ k, k < x → ¬ E k x) : (L * C) x x = L x x * C x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun k hk => ?_
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hC k x h (hx k h), mul_zero]
  · rw [hL x k h, zero_mul]

theorem mul_diag {E : Fin n → Fin n → Prop} {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R)
    (x : Fin n) (hx : ∀ l, x < l → ¬ E x l) : (C * R) x x = C x x * R x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun l hl => ?_
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hR l x h, mul_zero]
  · rw [hC x l h (hx l h), zero_mul]

theorem lo_diag_ne {M : Matrix (Fin n) (Fin n) K} (hM : Lo M) (hd : M.det ≠ 0) (i : Fin n) : M i i ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular M (fun i j h => hM i j (OrderDual.toDual_lt_toDual.1 h))] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

section Pair
variable {a b : Fin n} {L C R : Matrix (Fin n) (Fin n) K}

theorem lower_index_pair_unique (hab : (b : ℕ) = a + 1) : ∀ i j k : Fin n, (k = a ∧ j = b) → k ≤ i → i < j → (i = a ∧ j = b) := by
  rintro i j k ⟨rfl, rfl⟩ h1 h2
  refine ⟨Fin.ext ?_, rfl⟩
  rw [Fin.le_iff_val_le_val] at h1; rw [Fin.lt_iff_val_lt_val] at h2; omega

theorem l_aa (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a a = L a a * C a a :=
  diag_mul hL hC a fun _ _ e => absurd (congrArg Fin.val e.2) (by omega)

theorem l_ab (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a b = L a a * C a b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single a fun k hk => ?_
  have hk' : (k : ℕ) ≠ a := fun h => hk (Fin.ext h)
  rcases lt_or_gt_of_ne hk' with h | h
  · rw [hC k b (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hk e.1), mul_zero]
  · rw [hL a k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_ba (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b a = L b a * C a a + L b b * C b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k a (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_bb (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b b = L b a * C a b + L b b * C b b := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k b h (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem r_aa (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a a = C a a * R a a + C a b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 h) (fun e => hlb e.2), zero_mul]

theorem r_ab (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a b = C a b * R b b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single b fun l hl => ?_
  have hl' : (l : ℕ) ≠ b := fun h => hl (Fin.ext h)
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hR l b (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hl e.2), zero_mul]

theorem r_ba (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b a = C b a * R a a + C b b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC b l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hne e.1.symm), zero_mul]

theorem r_bb (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b b = C b b * R b b :=
  mul_diag hC hR b fun _ _ e => absurd (congrArg Fin.val e.1) (by omega)

end Pair

section Root
variable {ι : Type} {m : ι → ℕ} {τ : ι} {a b : Fin (m τ)}

theorem root_lower_pair_unique_left (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j k : Fin (m σ),
    ((⟨σ, k⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) → k ≤ i → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j k ⟨h1, h2⟩ hki hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨congrArg (Sigma.mk _) (Fin.ext ?_), rfl⟩
  rw [Fin.le_iff_val_le_val] at hki; rw [Fin.lt_iff_val_lt_val] at hij; omega

theorem root_lower_pair_unique_right (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j l : Fin (m σ),
    ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, l⟩ : Root m) = ⟨τ, b⟩) → j ≤ l → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j l ⟨h1, h2⟩ hjl hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨rfl, congrArg (Sigma.mk _) (Fin.ext ?_)⟩
  rw [Fin.le_iff_val_le_val] at hjl; rw [Fin.lt_iff_val_lt_val] at hij; omega

end Root

end GlobalTheory.FlagPush.LowMul

namespace GlobalTheory.FlagPush

open LowMul in

theorem almostLow_mul_entries : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  intro ι m τ a b hab K _ S T C hS hT hC
  have hSl : ∀ σ, Lo (S σ) := fun σ i j h => (hS σ).2.2.2 i j i.isLt h
  have hTl : ∀ σ, Lo (T σ) := fun σ i j h => (hT σ).2.2.2 i j i.isLt h
  have hCr : ∀ σ, AL (fun i j => (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) (C σ) :=
    fun σ => hC.2.2 σ
  have hCt : AL (fun i j => i = a ∧ j = b) (C τ) := fun i j h hn =>
    hC.2.2 τ i j h fun e => hn ⟨eq_of_heq (Sigma.mk.inj_iff.1 e.1).2, eq_of_heq (Sigma.mk.inj_iff.1 e.2).2⟩
  have hP : AL (fun i j => i = a ∧ j = b) (S τ * C τ) := al_mul (lower_index_pair_unique hab) (hSl τ) hCt
  have h3 : (S * C * T) τ a b = S τ a a * C τ a b * T τ b b := by
    show (S τ * C τ * T τ) a b = _
    rw [r_ab hab hP (hTl τ), l_ab hab (hSl τ) hCt]
  refine ⟨⟨fun σ => ?_, ?_, fun σ => ?_⟩, fun x hxa hxb => ?_, h3, ?_⟩
  · show (S σ * C σ * T σ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (hS.det_ne σ) (hC.1 σ)) (hT.det_ne σ)
  · rw [h3]
    exact mul_ne_zero (mul_ne_zero (lo_diag_ne (hSl τ) (hS.det_ne τ) a) hC.2.1) (lo_diag_ne (hTl τ) (hT.det_ne τ) b)
  · exact mul_al (root_lower_pair_unique_right hab σ) (al_mul (root_lower_pair_unique_left hab σ) (hSl σ) (hCr σ)) (hTl σ)
  · show (S x.1 * C x.1 * T x.1) x.2 x.2 = _
    rw [mul_diag (al_mul (root_lower_pair_unique_left hab x.1) (hSl x.1) (hCr x.1)) (hTl x.1) x.2 (fun _ _ e => hxa e.1),
      diag_mul (hSl x.1) (hCr x.1) x.2 (fun _ _ e => hxb e.2)]
  · show (S τ * C τ * T τ) a a * (S τ * C τ * T τ) b b - (S τ * C τ * T τ) a b * (S τ * C τ * T τ) b a =
      S τ a a * S τ b b * (C τ a a * C τ b b - C τ a b * C τ b a) * (T τ a a * T τ b b)
    rw [r_aa hab hP (hTl τ), r_bb hab hP (hTl τ), r_ab hab hP (hTl τ), r_ba hab hP (hTl τ),
      l_aa hab (hSl τ) hCt, l_bb hab (hSl τ) hCt, l_ab hab (hSl τ) hCt, l_ba hab (hSl τ) hCt]
    ring

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFiniteFrameLatticeForms
section
set_option autoImplicit false

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.UG Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame

theorem finite_forms_of_classes {O : Type} [CommRing O] {W : Type} [AddCommGroup W] [Module O W] [IsNoetherian O W]
    {G : Type} [Group G] (Γ K : Subgroup G) (ρ : Representation O K W)
    (h : ∃ S : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ κ ∈ K, g = γ * s * κ) : Module.Finite O (AMFK O Γ K ρ) := by
  obtain ⟨S, hS⟩ := h
  let ev : AMFK O Γ K ρ →ₗ[O] (S → W) :=
    (LinearMap.funLeft O W (Subtype.val : S → G)).comp (AMFK O Γ K ρ).subtype
  refine Module.Finite.of_injective ev ?_
  intro f f' hff
  ext g
  obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
  have h1 := f.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h2 := f'.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h3 : (f : G → W) s = (f' : G → W) s := congrFun hff ⟨s, hs⟩
  exact h1.trans ((congrArg _ h3).trans h2.symm)

theorem Frame.finite_latticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  intro l _ ι _ _ N F mu jK hF
  have : ∀ τ : ι, Module.Finite F.O (dualWeyl F.O N N (res N (mu τ))) :=
    fun τ => dualWeyl_module_finite F.O N N _
  have : IsNoetherian F.O (NablaT F.O N mu) := inferInstance
  exact finite_forms_of_classes F.Γ F.K _ hF.classes

end GlobalTheory.ExpFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumEqSumRationalRootTranslates
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdTh.MovedDatumCore
open GlobalTheory.AdTh.MovedDatum

theorem moved_datum_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → R.ωP i t (h, k) (R.vP i t) = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (R.ωP i t (h, k) (R.vacP i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourierCore.thetaVector_eq_sum_heisenberg_core D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun t l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  obtain ⟨hp, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i t hV
  obtain ⟨hψ, hvac⟩ := (hR.thP.vP i t).1
  rw [hδ t l φ hφ hP e he, map_smul]
  by_cases hfin : Finite (Fin (Vc D i).rank → LevQ Dw l)
  swap
  · haveI := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]
  rw [map_finsum _ (Set.toFinite _)]
  congr 1
  refine finsum_congr fun q => ?_
  rw [map_smul]
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨c, hc⟩ : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
      rw [hc, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s fun PP hPP => hs PP (Finset.mem_union.2 hPP))
    (γ q) (u q) (hu q).1 (hu q).2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (R.ωP i t (h, k) (R.vacP i)) =
      R.ωP i t (h, k) (R.vacP i) := by
    rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (R.ωP i t (h, k) (R.vacP i)) |>.trans
    (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  rw [hp.weil.om_heis h k _ _ hvac.theta]
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

end GlobalTheory.AdTh.MovedDatumCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory

theorem nat_le_four_of_dvd_of_embeddings_le_four :
    ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ) (r : 𝓞 F), y ≠ 0 → y = m * r →
    (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4) → m ≤ 4 := by
  intro F _ _ y m r hy hyr hφ
  set d := Module.finrank ℚ F with hd
  have hr : (r : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, mul_zero]
  have hm : (m : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, zero_mul]
  have hN : Algebra.norm ℚ y = (m : ℚ) ^ d * (Algebra.norm ℤ r : ℚ) := by
    rw [hyr, map_mul, Algebra.coe_norm_int]
    congr 1
    rw [show ((m : F)) = algebraMap ℚ F (m : ℚ) by simp, Algebra.norm_algebraMap]
  have hr0 : (Algebra.norm ℤ r : ℚ) ≠ 0 := by
    rw [Algebra.coe_norm_int]; exact (Algebra.norm_ne_zero_iff).2 hr
  have hr1 : (1 : ℝ) ≤ |((Algebra.norm ℤ r : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ r ≠ 0 := by exact_mod_cast hr0
    exact_mod_cast Int.one_le_abs this
  have hlow : (m : ℝ) ^ d ≤ |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    rw [hN]; push_cast
    rw [abs_mul, abs_pow, Nat.abs_cast]
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) d]
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have hup : |((Algebra.norm ℚ y : ℚ) : ℝ)| ≤ 4 ^ d := by
    have h1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ y)‖ = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
      simp
    rw [← h1, hprod, norm_prod]
    calc ∏ σ : F →ₐ[ℚ] ℂ, ‖σ y‖ ≤ ∏ _σ : F →ₐ[ℚ] ℂ, (4 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => hφ σ.toRingHom)
      _ = 4 ^ d := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card]
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have : (m : ℝ) ≤ 4 := (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) (by norm_num) hd0).1 (hlow.trans hup)
  exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroLocusSectionPullbackExtends
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelSecExt

open GlobalTheory.PrimSec GlobalTheory.AbLaw

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem genericPoint_mem_range (M : TrueGeo.Model Y) :
    haveI := M.ar.isIntegral; genericPoint M.X ∈ Set.range M.j := by
  haveI := M.ar.isIntegral
  have := M.ar.finite
  have := M.ar.isDomain
  haveI := HtSelfInter.charZero_residueField_genericPoint M.ar.charZero
  have h0 := Mean4O.asIdeal_eq_bot M.p (genericPoint M.X)
  have hr : genericPoint M.X ∈ Set.range (Limits.pullback.fst M.p (spMap (algebraMap (𝓞 F) F))) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext ?_⟩
    show Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, h0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  obtain ⟨z, hz⟩ := hr
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz, ← M.pb.isoPullback_inv_fst, Scheme.Hom.comp_apply]

theorem app_injective (M : TrueGeo.Model Y) (W : M.X.Opens) : Function.Injective (M.j.app W).hom := by
  haveI := M.ar.isIntegral
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne
  obtain ⟨y, hy⟩ := genericPoint_mem_range M
  have hb : M.X.basicOpen a ≠ ⊥ := fun h => hne ((basicOpen_eq_bot_iff a).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb
  have hη : genericPoint M.X ∈ M.X.basicOpen a := ((genericPoint_spec M.X).mem_open_set_iff (M.X.basicOpen a).isOpen).2 ⟨x, trivial, hx⟩
  have : y ∈ M.j ⁻¹ᵁ M.X.basicOpen a := by rw [Scheme.Hom.mem_preimage, hy]; exact hη
  rw [Scheme.preimage_basicOpen] at this
  change y ∈ Y.X.basicOpen ((M.j.app W).hom a) at this
  rw [ha, Scheme.basicOpen_zero] at this
  exact this

theorem exists_extension (M : TrueGeo.Model Y) {U : M.X.Opens} (t : Γ(Y.X, M.j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : M.X.Opens) (hV : V ≤ U) (b : Γ(M.X, V)), x ∈ V ∧
      (M.j.app V).hom b = rs Y.X (pre_le M.j hV) t) :
    ∃ b : Γ(M.X, U), (M.j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hc : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := M.X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hc (fun x => b x.1 x.2) (fun x y => by
      apply app_injective M
      refine (app_rs M.j inf_le_left _).trans (Eq.trans ?_ (app_rs M.j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, Y.X.sheaf.eq_of_locally_eq' (fun x : U => M.j ⁻¹ᵁ V x.1 x.2) (M.j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨M.j y, hy⟩, hx _ hy⟩
  · exact (app_rs M.j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

end GlobalTheory.ModelSecExt

open GlobalTheory.PrimSec GlobalTheory.AbLaw GlobalTheory.ModelSecExt in

theorem GlobalTheory.ModelSecExt.main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (B : LB M.X),
    B.IsLB → ∀ t : (B.pull M.j).Sec, ∃ s : B.Sec, ∀ y : Y.X,
      M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  intro F _ _ Y M B hB t
  haveI := M.ar.isIntegral
  haveI := M.ar.isNoetherian
  have hx : ∀ x : M.X, ∃ (i : B.ι) (W : M.X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      M.X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
    exact ⟨i, W, hW, hxW, hWU⟩
  choose ci Wx hWa hxW hWle using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set M.X)) (fun x => (Wx x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  choose π b hπ hb using fun x => exists_numerator M.pb (hWa x) (loc t (ci x) (hWle x))
  classical
  let c : 𝓞 F := ∏ x ∈ S, π x
  have hc : algebraMap (𝓞 F) F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun x _ => hπ x
  have hb' : ∀ x ∈ S, ∃ b' : Γ(M.X, Wx x), (M.j.app (Wx x)).hom b' =
      cst Y.str (M.j ⁻¹ᵁ Wx x) (algebraMap (𝓞 F) F c) * loc t (ci x) (hWle x) := by
    intro x hxS
    refine ⟨cst M.p (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩
    rw [map_mul, app_cst M.pb.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]
  choose! b' hb' using hb'
  have key : ∀ i, ∃ s : Γ(M.X, B.U i), (M.j.app (B.U i)).hom s =
      cst Y.str (M.j ⁻¹ᵁ B.U i) (algebraMap (𝓞 F) F c) * loc t i le_rfl := by
    intro i
    refine exists_extension M _ fun x hx => ?_
    obtain ⟨z, hzS, hxz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    have hV : B.U i ⊓ Wx z ≤ B.U i := inf_le_left
    have hk : B.U i ⊓ Wx z ≤ B.U (ci z) := inf_le_right.trans (hWle z)
    refine ⟨B.U i ⊓ Wx z, hV, rs M.X (le_inf hV hk) (B.g i (ci z)).val * rs M.X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩
    rw [map_mul, app_rs M.j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst, rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst,
      rs_loc t i le_rfl hV,
      loc_trans t i (ci z) (le_rfl.trans hV) hk]
    ring
  choose s hs using key
  have hunit : ∀ W : Y.X.Opens, IsUnit (cst Y.str W (algebraMap (𝓞 F) F c)) := fun W =>
    (IsUnit.mk0 _ hc).map _
  refine ⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩
  · apply app_injective M
    change (M.j.app _).hom (rs M.X inf_le_left (s i)) = (M.j.app _).hom (_ * rs M.X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst,
      rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]
    ring
  · have hmem : ∀ i, y ∈ M.j ⁻¹ᵁ B.U i →
        (M.j y ∈ M.X.basicOpen (s i) ↔ y ∈ Y.X.basicOpen (t.f (fun _ => i))) := by
      intro i hy
      change y ∈ M.j ⁻¹ᵁ M.X.basicOpen (s i) ↔ _
      rw [Scheme.preimage_basicOpen]
      change y ∈ Y.X.basicOpen ((M.j.app (B.U i)).hom (s i)) ↔ _
      rw [hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]
      exact ⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩
    constructor
    · intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ M.j ⁻¹ᵁ B.U i := M.X.basicOpen_le (s i) hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩
    · intro h
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ M.j ⁻¹ᵁ B.U (k PUnit.unit) := Set.mem_iInter.1 (Y.X.basicOpen_le (t.f k) hk) PUnit.unit
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPos
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem poinWt_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) →
    (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  intro n S v hS
  refine ⟨fun a => ?_, fun hne a => ?_⟩
  · unfold poinWt
    split_ifs with ha
    · refine ⟨mul_nonneg (norm_nonneg _) (abs_nonneg _), ?_⟩
      rcases (norm_nonneg (v a)).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have h1 : ‖v a‖ ≤ 1 := (hS a ha).trans (by norm_num)
        have := Real.abs_log_mul_self_lt _ hpos h1
        rw [abs_mul, abs_of_pos hpos] at this
        linarith
    · exact ⟨zero_le_one, le_rfl⟩
  · unfold poinWt
    split_ifs with ha
    · have hpos : 0 < ‖v a‖ := norm_pos_iff.mpr (hne a ha)
      have hlt : ‖v a‖ < 1 := (hS a ha).trans_lt (by norm_num)
      have hlog : Real.log ‖v a‖ < 0 := Real.log_neg hpos hlt
      exact mul_pos hpos (abs_pos.mpr hlog.ne)
    · exact zero_lt_one

end GlobalTheory.GoodTop
end

