import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3420
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3425
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermValuesEqOfLocalIdentity
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem sval_eq_of_localIdentity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → ∀ c : ℕ → Q.X → R, (∀ (i : h.J) (i' : h'.J) (k : ℕ) (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ (c k α) * f)) → ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (c k α)) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y n v dd hv D h h' hb hb' c hc k α σ σ' σ'' ⟨τ₁, τ₁', t1, t1', a1⟩ ⟨τ₂, τ₂'', t2, t2'', a2⟩ T x z J hJ
  refine GlobalTheory.T.raynaudProjection_sectionValues_identity R Q O oa Y k α σ σ' σ'' (c k α) ?_ T x z J hJ
  intro y J' hJ'
  have e : ∀ (s : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α s τ →
      sval τ (𝟙 Y.H.left) y J' = sval s Y.q.left y J' * (val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J').val := by
    intro s τ hτ
    have := hτ Y.H (𝟙 _) y J' hJ'
    simpa only [Over.id_left, Category.id_comp] using this
  have key := GlobalTheory.T.heatOperators_related_fourierTerm_images R Q O oa Y n dd D (fun a => (hv a).1) h h' hb hb' k α (c k α) (fun i i' => hc i i' k α) τ₁ τ₁' τ₂ τ₂''
    (fun y J hJ => by
      have a := t1 Y.H (𝟙 _) y J hJ
      have b := t2 Y.H (𝟙 _) y J hJ
      simp only [Over.id_left, Category.id_comp] at a b
      rw [a, b])
    (GlobalTheory.T.raynaudFourierTerm_localFunction_isWeight R Q O oa Y k α σ τ₂ t2) a1 a2 y J' hJ'
  rw [e σ' τ₁' t1', e σ'' τ₂'' t2'', e σ τ₂ t2] at key
  set u := val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J'
  have : (sval σ' Y.q.left y J' - (sval σ'' Y.q.left y J' + gs (𝟙 _) y ⊤ (scal Y.H.hom (c k α)) * sval σ Y.q.left y J')) * u.val = 0 := by
    rw [sub_mul, key]; ring
  have h0 := congrArg (· * (u⁻¹ : (Y.H.left.presheaf.stalk y)ˣ).val) this
  simp only [Units.mul_inv_cancel_right, zero_mul] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.Heat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatLoc

variable {F : Type} [Field F]

theorem der_bracket (d : Derivation ℤ F F) (x y β : F) (M : ℕ) :
    x * β ^ M * d (y * β ^ M) - y * β ^ M * d (x * β ^ M) = β ^ (2 * M) * (x * d y - y * d x) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem der_mul_pow (d : Derivation ℤ F F) (x β : F) (hβ : β ≠ 0) (m : ℕ) :
    d (x * β ^ (m + 1)) = β ^ (m + 1) * (d x + ((m + 1 : ℕ) : F) * x * (d β / β)) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  field_simp
  ring

theorem symb_eq {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (hβ : β ≠ 0) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * (x * β ^ (m + 1)) * (x * β ^ (m + 1) * δ₀ (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ₀ (x * β ^ (m + 1))) -
      ∑ a, ∑ e, Λ a e * δ a (x * β ^ (m + 1)) *
        (x * β ^ (m + 1) * δ e (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ e (x * β ^ (m + 1))) =
    β ^ (3 * (m + 1)) * (((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x)) := by
  rw [mul_sub (β ^ (3 * (m + 1))), Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · rw [der_bracket]; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [der_bracket, der_mul_pow _ _ _ hβ]; ring

theorem symb_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * 1 * (1 * δ₀ y - y * δ₀ 1) -
      ∑ a, ∑ e, Λ a e * (δ a 1 + ((m + 1 : ℕ) : F) * 1 * (δ a β / β)) * (1 * δ e y - y * δ e 1) =
    ((m + 1 : ℕ) : F) * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) := by
  simp only [Derivation.map_one_eq_zero, mul_zero, sub_zero, zero_add, one_mul, mul_one]
  rw [mul_sub, Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · push_cast; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring

def derivationBracketSum {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) : F :=
  ∑ a, ∑ e, Λ a e * δ a x * (x * δ e y - y * δ e x)

theorem symb_two {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
    ((m + 1 : ℕ) : F) * x * (x * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) -
      y * ((k : F) * δ₀ x - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x)) - derivationBracketSum δ Λ x y := by
  have hs : ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
      derivationBracketSum δ Λ x y + ((m + 1 : ℕ) : F) * x * (x * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y -
        y * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x) := by
    unfold derivationBracketSum
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs]; push_cast; ring

theorem tsum_add_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) :
    derivationBracketSum δ Λ (x + 1) y - derivationBracketSum δ Λ x y = ∑ a, ∑ e, Λ a e * δ a x * δ e y := by
  unfold derivationBracketSum
  simp only [map_add, Derivation.map_one_eq_zero, add_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  ring

end GlobalTheory.HeatLoc

namespace GlobalTheory.HeatLoc

theorem valR_ne_zero_sec {X : Scheme.{0}} (L : LB X) {F : Type} [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι)
    (h : ⊤ ≤ ξ ⁻¹ᵁ L.U j₀) (k : ℕ) (s : SecM (𝟙 X) L k) (hs : ⊤ ≤ ξ ⁻¹ᵁ nonzeroLocus s) :
    valR ξ _ (s.f fun _ => j₀) ≠ 0 := by
  have hk : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) fun _ => (k : ℤ)).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => h hp
  have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff ξ (IsLocalRing.closedPoint F) _ (hk trivial) _).1
    ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs s ξ _ (hk trivial)).1 (hs trivial))
  exact ((GlobalTheory.Points.le_preimage_basicOpen_iff ξ hk _).1
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of F) ξ h₁).ge).ne_zero

theorem symb_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  intro K _ _ P₀ n v dd hdd F _ ψ ξ hξ hinj δ hδ j₀ hj₀ δ₀ Λ hyp k hk s hs
  haveI := P₀.isAb.proper
  haveI : CompactSpace P₀.A.left := QuasiCompact.compactSpace_of_compactSpace P₀.A.hom
  haveI : QuasiSeparatedSpace P₀.A.left := quasiSeparatedSpace_of_quasiSeparated P₀.A.hom
  obtain ⟨G₁, G₂⟩ := GlobalTheory.T.pointValue_eq_quotient_section_by_power_at_field P₀.A.left P₀.L P₀.isLB F ξ j₀ hj₀ k s hs
  have hβ := valR_ne_zero_sec P₀.L ξ j₀ hj₀ k s hs
  set β := valR ξ _ (s.f fun _ => j₀) with hβdef
  have v1 : valR ξ (nonzeroLocus s) 1 = 1 := by rw [WtAlg.valR_eq' ξ _ hs, map_one, map_one]
  have hM : ∀ m : ℕ, ((m + 1 : ℕ) : F) ≠ 0 := fun m h => by
    have : ψ ((m + 1 : ℕ) : K) = 0 := by rw [map_natCast]; exact h
    exact (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)) ((map_eq_zero ψ).1 this)

  have partD : ∀ f : Γ(P₀.A.left, nonzeroLocus s), ∃ f' : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f) := by
    intro f
    obtain ⟨m₁, h₁⟩ := G₁ 1
    obtain ⟨m₂, h₂⟩ := G₁ f
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, v1, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_one] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * ((k : F) * δ₀ (valR ξ _ f) -
        ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f)) := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨constFn P₀.A.hom _ (((m + 1 : ℕ) : K)⁻¹) * g, ?_⟩
    rw [WtAlg.valR_mul'' ξ _ hs, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ hs hξ, e', map_inv₀, map_natCast,
      ← _root_.mul_assoc, inv_mul_cancel₀ (hM m), _root_.one_mul]

  have partT : ∀ f f' : Γ(P₀.A.left, nonzeroLocus s), ∃ h : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ h = derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
    intro f f'
    obtain ⟨m₁, h₁⟩ := G₁ f
    obtain ⟨m₂, h₂⟩ := G₁ f'
    obtain ⟨d, hd⟩ := partD f
    obtain ⟨d', hd'⟩ := partD f'
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_two, ← hd, ← hd'] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * valR ξ _ f * (valR ξ _ f * valR ξ _ d' - valR ξ _ f' * valR ξ _ d) -
        derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨((m + 1 : ℕ) : Γ(P₀.A.left, nonzeroLocus s)) * f * (f * d' - f' * d) - g, ?_⟩
    rw [WtAlg.valR_sub' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_sub' ξ _ hs,
      WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_natCast' ξ _ hs, e']
    ring
  refine ⟨fun f f' => ?_, partD⟩
  obtain ⟨h₁, e₁⟩ := partT (f + 1) f'
  obtain ⟨h₂, e₂⟩ := partT f f'
  refine ⟨h₁ - h₂, ?_⟩
  rw [WtAlg.valR_sub' ξ _ hs, e₁, e₂, WtAlg.valR_add' ξ _ hs, v1, tsum_add_one]

end GlobalTheory.HeatLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumIsoAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem linHom_unique (hR : Base R) (hG : IsSemiAbelian G) {U : Unif (maximalIdeal R) D A G} {a a' k k' g g'}
    (h : LinHom U.toUnifPre U.toUnifPre a k g) (h' : LinHom U.toUnifPre U.toUnifPre a' k' g') (ha : a = a')
    (hk : ∀ y, k y = k' y) : g = g' := by
  obtain rfl := ha
  obtain rfl : k = k' := AddMonoidHom.ext hk
  obtain ⟨u₁, u₂⟩ := GlobalTheory.MumUniq.main R hR.1 D A G hG U a k
  exact u₂ g g' (congrFun (u₁ _ _ (linHom_iff_linEnd.1 h).2 (linHom_iff_linEnd.1 h').2))

end

theorem iso_of_factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi A₀ G₀ _ _ hG₀ U₀
  obtain ⟨-, hsym, g, hg⟩ := hF
  obtain ⟨u, u', hu, hu', hadj⟩ :=
    GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm R hR D' A' G' hG' U' D A₀ G₀ hG₀ U₀ _ _ _ _ (GlobalTheory.T.idempotentFactor_projection_adjointPair R _ D D' F)
  have hO : ∀ a : F.O, LinHom U'.toUnifPre U'.toUnifPre (F.o.onB.act a)
      (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hu1 := hu.1
  have hu1' := hu'.1
  have hee : Star.star F.e * Star.star F.e = Star.star F.e := by rw [← star_mul, F.idem]
  have hsS : Star.star (Star.star F.e * F.f * F.e) = Star.star F.e * F.f * F.e := by
    rw [star_mul, star_mul, star_star, ← _root_.mul_assoc, ← hsym]
  have hsg : (Star.star F.e * F.f * F.e) * Star.star g = Star.star F.e := by
    have := congrArg Star.star hg
    rwa [star_mul, hsS] at this
  have hkey : F.e * Star.star g * (Star.star F.e * F.f * F.e) = F.e := by
    calc F.e * Star.star g * (Star.star F.e * F.f * F.e)
        = g * ((Star.star F.e * F.f * F.e) * Star.star g) * (Star.star F.e * F.f * F.e) := by
          nth_rewrite 1 [← hg]; simp only [_root_.mul_assoc]
      _ = g * (Star.star F.e * (Star.star F.e * F.f * F.e)) := by rw [hsg, _root_.mul_assoc]
      _ = F.e := by
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e * F.f) F.e,
            ← _root_.mul_assoc (Star.star F.e) (Star.star F.e) F.f, hee, hg]
  have hxi : ∀ y, F.xi y = F.e • F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  have hincE : F.inc ≫ F.o.onB.act F.e = F.inc := by
    rw [← F.pr_inc, ← Category.assoc, F.inc_pr, Category.id_comp]
  have h1 : u ≫ u' = oG.act (Star.star F.e * F.f * F.e) :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG' (hu.comp hu') (hO _)
      (by rw [F.o.onB.map_mul (Star.star F.e * F.f) F.e, ← F.pr_inc]; exact (Category.assoc _ _ _).symm)
      (fun y => by
        change (Star.star F.e * F.f) • F.xi (F.xp y) = Star.star (Star.star F.e * F.f * F.e) • y
        rw [hsS, F.xi_xp, smul_smul])
  have h2 : u' ≫ oG.act (F.e * g) ≫ u = 𝟙 G₀ :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG₀ ((hu'.comp (hO _)).comp hu) (LinHom.id _)
      (by
        calc ((F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) ≫ F.o.onB.act (F.e * g)) ≫ F.pr
            = F.inc ≫ F.o.onB.act ((F.e * g) * (Star.star F.e * F.f * F.e)) ≫ F.pr := by
              rw [F.o.onB.map_mul (F.e * g) (Star.star F.e * F.f * F.e),
                F.o.onB.map_mul (Star.star F.e * F.f) F.e]
              conv_lhs => rw [← hincE]
              simp only [Category.assoc]
          _ = 𝟙 _ := by
              rw [_root_.mul_assoc F.e g, hg, F.idem, ← F.pr_inc]
              simp only [← Category.assoc, F.inc_pr, Category.id_comp])
      (fun y => by
        change F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y)) = y
        have hw : Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y) =
            (Star.star g * (Star.star F.e * F.f * F.e)) • F.xi y := by
          conv_lhs => rw [hxi y]
          rw [smul_smul, smul_smul, star_mul]
          congr 1
          simp only [_root_.mul_assoc]
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e), hee]
        have h3 : F.xi (F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y))) = F.xi y := by
          rw [F.xi_xp, hw, smul_smul, ← _root_.mul_assoc, hkey, ← hxi]
        have := congrArg F.xp h3
        rwa [F.xp_xi, F.xp_xi] at this)
  refine ⟨⟨inc ≫ u, u' ≫ oG.act g ≫ pr, ?_, ?_⟩, u, u', inferInstance, hu.1, hu'.1, rfl, h1, hadj⟩
  · calc (inc ≫ u) ≫ u' ≫ oG.act g ≫ pr = inc ≫ ((u ≫ u') ≫ oG.act g) ≫ pr := by simp only [Category.assoc]
      _ = 𝟙 G := by
          rw [h1, ← oG.map_mul, hg, ← hpi]
          simp only [← Category.assoc, hip, Category.id_comp]
  · calc (u' ≫ oG.act g ≫ pr) ≫ inc ≫ u = u' ≫ (oG.act g ≫ pr ≫ inc) ≫ u := by simp only [Category.assoc]
      _ = 𝟙 G₀ := by rw [hpi, ← oG.map_mul, h2]

end GlobalTheory.MumIsoAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastFurther
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiCoordRescaleLocal

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (q : D.X → (FractionRing R)ˣ) (y : D.X),
    PsiUnitOn D y Set.univ → ∀ s : R, (q y : FractionRing R) = algebraMap R (FractionRing R) s →
      ∃ u : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.PolDeg.rescale D q) y (u * s) := by
  intro R _ _ _ D q y h s hs
  obtain ⟨v, hv⟩ := GlobalTheory.LocM.FJ.MultiData.exists_unit_psiCoord D y h
  have h2 := GlobalTheory.LocM.FJ.MultiData.psiCoord_rescale D q hv hs
  refine ⟨v, ?_⟩
  rw [mul_comm]
  exact h2

end GlobalTheory.PsiCoordRescaleLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntClosureAutExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem intClosure_aut_extends : ∀ (o₁ Ω₁ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (z₁ : M₁.Z), letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ σ : (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[M₁.Z.presheaf.stalk z₁] (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂), ∃ σ' : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, σ' (b : Ω₂) = ((σ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : Ω₂) := by
  intro o₁ Ω₁ _ _ _ Ω₂ _ _ _ M₁ z₁ σ
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₁ := (M₁.stalkHom z₁).toAlgebra
  haveI : IsDomain (M₁.Z.presheaf.stalk z₁) := (M₁.stalkHom_injective z₁).isDomain _
  haveI : FaithfulSMul (M₁.Z.presheaf.stalk z₁) Ω₁ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M₁.stalkHom_injective z₁)
  haveI : IsFractionRing (M₁.Z.presheaf.stalk z₁) Ω₁ := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M₁.O z₁) x
    refine ⟨(M₁.stalkEquiv z₁).symm a, (M₁.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : M₁.O z₁, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₁ ((M₁.stalkEquiv z₁).symm c) = c := fun c => by
      change M₁.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic Ω₁ Ω₂ := inferInstance
  refine ⟨(galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ, fun b => ?_⟩
  have := algebraMap_galRestrict_apply (M₁.Z.presheaf.stalk z₁)
    ((galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ) b
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFieldBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FieldCompat

open GlobalTheory.CechKS GlobalTheory.LogKSBal

theorem isTr_comp {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ G.left) (hm : IsGrpPullback A G (spMap x₀) m)
    (w : TanM (𝟙 (Sp R)) G) (v : epsR K ⟶ A)
    (hv : v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTransl φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w (y ≫ m) := by
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hy
  have dc : (dualMap φ).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) = dualMap (φ.comp x₀) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  obtain ⟨p, q, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ spMap x₀
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp'])
  refine ⟨p, q, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← GlobalTheory.LogKSLoc.spMap_comp' (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hv]
    exact (Category.assoc (spMap (dualMap φ)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀)) _).symm

theorem invField_baseChange : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := by
  intro R _ K _ x₀ G _ _ A _ _ m hm w e he v hvt hv dd hdd O f
  refine ext_valR _ _ fun B _ y hy => ?_
  have hb : y ≫ A.hom = spMap (Spec.preimage (y ≫ A.hom)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ A.hom)).hom = β at hb
  obtain ⟨y', hy'⟩ := exists_isTransl β y hb v
  have hO : ⊤ ≤ y' ⁻¹ᵁ (m ⁻¹ᵁ O) := le_preimage_of_red (hy'.red hvt) hy
  rw [← snd_valR_transl hvt hdd hy' hy, CoeffWt.valR_app _ _ _ hO, valR_pbT y m le_rfl hy]
  refine he.2 B (β.comp x₀) (y ≫ m) (y' ≫ m) O f ?_ hy (isTr_comp x₀ m hm w v hv β y hb y' hy')
  rw [Category.assoc, hm.1.w, ← Category.assoc, hb, GlobalTheory.LogKSLoc.spMap_comp']

end GlobalTheory.Heat.FieldCompat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldPullbackAlongGroupHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.PullField

theorem isInv_pbT_single : ∀ (R : Type) [CommRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q] (v : TanM (𝟙 (Sp R)) G) (u : TanM (𝟙 (Sp R)) B) (dd : Fld G.left) (e : Fld B.left), tv v ≫ q = tv u → IsInv G v dd → IsInv B u e → ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V), dd W (pbT q.left f W) = pbT q.left (e V f) W := by
  intro R _ G B _ _ _ _ q _ v u dd e hvu hd he V W hW f
  have hc : GlobalTheory.Heat.LiePush.pushL q v = ∑ a : Fin 1, (fun _ => (1 : R)) a • (fun _ => u) a := by
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext hvu
  rw [GlobalTheory.Heat.LiePush.isInv_pbT q hd (fun _ => he) (fun _ => 1) hc V f W hW]
  congr 1
  simp only [Finset.univ_unique, Finset.sum_singleton]
  simp [constFn]

end GlobalTheory.Heat.PullField
end
end

