import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobXiEigenvectorEqOfFrameImageEqStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobXi_eigenvector_eq_of_frame_image_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := by
  first | exact @GlobalTheory.WinLift.eigen_eq_of_frame_eq | exact GlobalTheory.WinLift.eigen_eq_of_frame_eq | (intros; apply GlobalTheory.WinLift.eigen_eq_of_frame_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCongruenceCombinationOverIntegersStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_congruence_combination_over_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ (W : Fin d ⊕ Fin k → F.B) (b : Fin k → F.B), (∀ l, ¬IsUnit (F.θ (W l))) → In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb W e) → In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => 0) b) e)) - frob p F.s (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e))) → ∃ (F₁ : MvPowerSeries (Fin d ⊕ Fin d) F.B) (t : MvPowerSeries (Fin d) O), map (algebraMap F.B F.Q) F₁ = cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e) ∧ (∀ i, ¬IsUnit (lin t i)) ∧ (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - F.θ (coeff β F₁) ^ p)) ∧ ∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t)) := by
  first | exact @GlobalTheory.SmallSecond.frob_congr_to_O | exact GlobalTheory.SmallSecond.frob_congr_to_O | (intros; apply GlobalTheory.SmallSecond.frob_congr_to_O <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftSolvesModFrobXiMuStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_lift_solves_mod_frobXi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := by
  first | exact @GlobalTheory.WinLift.frob_lift_dvd | exact GlobalTheory.WinLift.frob_lift_dvd | (intros; apply GlobalTheory.WinLift.frob_lift_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Functor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFam

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀}
  {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (hπ : IsNilpotent (RingHom.ker π))
  {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) (ν : K₀.K → K.K)
  (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D)
  (hc : ∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1)

def obj (T : K₀.Obj) : K.Obj where
  k := ν T.k
  C := T.ten D
  alg := ((algebraMap D (T.ten D)).comp τV).toAlgebra
  J := T.tenJ π
  nil := T.tenJ_nil π hπ
  ρ := ((Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc).comp (Ta T.k)).toRingHom
  ρ_cst f := by
    change Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc (Ta T.k (K.cst (ν T.k) f)) = τV f ⊗ₜ[ℂ] (1 : T.C)
    rw [hc, Algebra.TensorProduct.map_tmul, map_one]
    rfl

variable (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k))
  (hd : ∀ k a h, Ta k (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta k h))
  (hcl : ∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom))

include hd hcl in

theorem close {T T' : K₀.Obj} (f : T ⟶ T') :
    Close (T'.tenJ π) ((obj π hπ K ν Ta τV hc T').ρ.comp (Charts.sh (hν _ _ _ (Charts.Hom.le f))))
      ((Charts.Hom.ten D f : T.ten D →+* T'.ten D).comp (obj π hπ K ν Ta τV hc T).ρ) := by
  have h1 := (hcl _ _ _ (Charts.Hom.le f)).map (J' := T'.tenJ π)
    (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom (fun c hc' ↦ by
      have : (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W T'.k)) ≤
          (T'.tenJ π).comap (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom :=
        Ideal.map_le_iff_le_comap.2 fun d hd' ↦ by
          change T'.red π (d ⊗ₜ T'.ρc 1) ∈ T'.J
          rw [Charts.Obj.red_tmul, (RingHom.mem_ker).1 hd', map_zero, zero_mul]
          exact T'.J.zero_mem
      exact this hc')
  have h2 := GlobalTheory.AnPer.Close.tensor_comp (Ta T.k) (hd T.k) T'.J (T'.tenJ π) (fun c hc' ↦ by
      change T'.red π (1 ⊗ₜ c) ∈ T'.J
      rw [Charts.Obj.red_tmul]
      exact T'.J.mul_mem_left _ hc')
    (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k)) (K₀.maps (Charts.Hom.le f))))
    ((Charts.Hom.φc f).comp T.ρc) f.close
  have e1 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc
      (Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f))) x) = Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f)))) x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d c => rfl
  have e2 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) ((Charts.Hom.φc f).comp T.ρc) x =
      Charts.Hom.ten D f (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d c => rfl
  have tr : ∀ {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C} {a b b' c c' : Hol W →+* C},
      Close J a b → Close J b' c → (∀ h, b h = b' h) → (∀ h, c h = c' h) → Close J a c' := by
    intro W C _ J a b b' c c' p q e e'
    obtain rfl : b = b' := RingHom.ext e
    obtain rfl : c = c' := RingHom.ext e'
    exact Relation.ReflTransGen.trans p q
  exact tr h1 h2 (fun h ↦ e1 (Ta T.k h)) (fun h ↦ e2 (Ta T.k h))

def functor : K₀.Obj ⥤ K.Obj where
  obj := obj π hπ K ν Ta τV hc
  map {T T'} f :=
    { φ := { (Charts.Hom.ten D f : T.ten D →+* T'.ten D) with commutes' := fun d ↦ (Charts.Hom.ten D f).commutes (τV d) }
      deg := f.deg
      le := hν _ _ _ (Charts.Hom.le f)
      mem := fun _ h ↦ Charts.Hom.ten_mem π f h
      close := close π hπ K ν Ta τV hc hν hd hcl f }
  map_id T := Charts.hom_ext (fun b ↦ mp_id (K₀.Ten D) T b) rfl
  map_comp f f' := Charts.hom_ext (fun b ↦ mp_comp (K₀.Ten D) f f' b) rfl

def coef : CoefMap τV K.Oc (K₀.Ten D) where
  G := functor π hπ K ν Ta τV hc hν hd hcl
  α T := RingHom.id (T.ten D)
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.ten D) (τV b) c).symm

theorem main : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (r : Real K s σ) (ν : K₀.K → K.K) (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k)) (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D), (∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1) → (∀ k a h, Ta k (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta k h)) → (∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom)) → ∀ (φ₀ : X₀ ⟶ X), (∀ k, spMap ((Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W k))).comp π) (AlgHom.id ℂ (Hol (K₀.W k))) (fun _ _ ↦ Commute.all _ _)).comp (Ta k)).toRingHom ≫ r.x (ν k) = r₀.x k ≫ φ₀) → ∀ (j : B →+* D₀) (n : IsMor (dp0 B) s κ s' j φ₀), (∀ b, io (j b) = τV (σ b)) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V) (q : Λ →+ D), (∀ l, q l = τV (per l)) → r.coef.pull1 c = K.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (n.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ I _ F K B _ X s σ r ν hν Ta τV hc hd hcl φ₀ hpt
    j n hj c per q hq hper
  let β := coef π hπ K ν Ta τV hc hν hd hcl
  let θ : (r.coef.comp β).G ⟶ (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { RingHom.id (T.ten D) with commutes' := fun b ↦ congrArg (algebraMap D (T.ten D)) (hj b).symm }
          φ₀ := Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl
          comm := fun _ ↦ rfl
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat _ (T.tenδ π) (RingHom.id (T.ten D)) fun _ h ↦ h
          pt := by
            have e : (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl).comp
                ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) =
                ((Ideal.Quotient.mk T.J).comp T.ρ).comp ((Algebra.TensorProduct.lift
                  ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π) (AlgHom.id ℂ (Hol (K₀.W T.k)))
                  (fun _ _ ↦ Commute.all _ _)).comp (Ta T.k)).toRingHom := by
              have e' : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), T.red π (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) =
                  T.ρc (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π)
                    (AlgHom.id ℂ (Hol (K₀.W T.k))) (fun _ _ ↦ Commute.all _ _) x) := fun x ↦ by
                induction x using TensorProduct.induction_on with
                | zero => simp only [map_zero]
                | add x y hx hy => simp only [map_add, hx, hy]
                | tmul d c =>
                  rw [Algebra.TensorProduct.lift_tmul, map_mul]
                  exact congrArg (· * T.ρc c) (T.ρc.commutes (π d)).symm
              exact RingHom.ext fun h ↦ congrArg (Ideal.Quotient.mk T.J) (e' (Ta T.k h))
            change spMap (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl) ≫
              spMap ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) ≫ r.x (ν T.k) =
              (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₀.x T.k) ≫ φ₀
            rw [Category.assoc, ← hpt]
            exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r.x (ν T.k)) ((Cris.spMap_comp _ _).symm.trans
              ((congrArg spMap e).trans (Cris.spMap_comp _ _)))).trans (Category.assoc _ _ _)) }
      naturality := fun _ _ _ ↦ Thick.hom_ext fun _ ↦ rfl }
  have h1 := (r.coef.comp β).pullCohomologyOne_eq_of_natTrans (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)) θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp, hper] at h1
  refine h1.symm.trans (congrArg (GlobalTheory.CatCoh.H1.mk _) (Subtype.ext ?_))
  funext T T' f
  change algebraMap D (T'.ten D) (τV (per f.deg)) = algebraMap D (T'.ten D) (q f.deg)
  rw [hq]

end GlobalTheory.AnPer.TenFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportSecondEisensteinCmStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transport_second_eisenstein_cm : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  first | exact @GlobalTheory.NormSqOfSquareEqNeg.main | exact GlobalTheory.NormSqOfSquareEqNeg.main | (intros; apply GlobalTheory.NormSqOfSquareEqNeg.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharacterCoxeterTorusInvEqAtInverse
section
open Polynomial

noncomputable section

namespace GlobalTheory.CuspInv

open GlobalTheory.IndefiniteRowSideFullHecke

def mirrorEquiv (k : Type) [Field k] : k[X] ≃* k[X] where
  toFun := mirror
  invFun := mirror
  left_inv := fun f => mirror_mirror f
  right_inv := fun f => mirror_mirror f
  map_mul' := fun f g => mirror_mul_of_domain f g

theorem powIrr_of_inv {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι] (h h' : Matrix ι ι k)
    (hh : h * h' = 1) (H : ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n) :
    ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h'.charpoly = φ ^ n := by
  classical
  obtain ⟨φ, n, hφ, hn⟩ := H
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (Matrix.isUnit_det_of_right_inverse hh)
  have hinv : h' = h⁻¹ := (Matrix.inv_eq_right_inv hh).symm
  have hdet : h.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hh).ne_zero
  have h0 : h.charpoly.coeff 0 ≠ 0 := by
    intro h0
    exact hdet (by rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero])
  have hm : h.charpoly.mirror = h.charpolyRev := by
    rw [mirror, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (p := h.charpoly) h0, pow_zero, mul_one,
      Matrix.reverse_charpoly]
  have hψ : Irreducible (mirrorEquiv k φ) := (MulEquiv.irreducible_iff (mirrorEquiv k)).2 hφ
  have h1 : h.charpolyRev = (mirrorEquiv k φ) ^ n := by
    rw [← map_pow, ← hn, ← hm]; rfl
  have hass : Associated h'.charpoly ((normalize (mirrorEquiv k φ)) ^ n) := by
    refine Associated.trans ?_ ((associated_normalize _).pow_pow)
    rw [hinv, Matrix.charpoly_inv h hu, h1]
    refine associated_unit_mul_left _ _ ?_
    refine IsUnit.mul (IsUnit.pow _ isUnit_one.neg) ?_
    rw [isUnit_C, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
    exact inv_ne_zero hdet
  refine ⟨normalize (mirrorEquiv k φ), n, (associated_normalize _).irreducible hψ, ?_⟩
  exact eq_of_monic_of_associated h'.charpoly_monic ((monic_normalize hψ.ne_zero).pow n) hass

theorem eigenspace_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : g * f = 1) (z : L) : f.eigenspace z ≤ g.eigenspace z⁻¹ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : g (f v) = v := by rw [← Module.End.mul_apply, hfg]; rfl
  rw [hv, map_smul] at h1
  by_cases hz : z = 0
  · subst hz
    rw [zero_smul] at h1
    rw [← h1]; simp
  · conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]

theorem eigenspace_inv {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : f * g = 1) (hgf : g * f = 1) (z : L) : g.eigenspace z⁻¹ = f.eigenspace z := by
  refine le_antisymm ?_ (eigenspace_le f g hgf z)
  simpa using eigenspace_le g f hfg z⁻¹

theorem mem_aroots_iff {k L ι : Type} [Field k] [Field L] [Algebra k L] [Fintype ι] [DecidableEq ι]
    (h : Matrix ι ι k) (z : L) :
    z ∈ h.charpoly.aroots L ↔
      Module.End.eigenspace (Matrix.toLin' (h.map (algebraMap k L))) z ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_toLin', Matrix.charpoly_map, mem_aroots, IsRoot, eval_map_algebraMap]
  simp [h.charpoly_monic.ne_zero]

theorem torVal_inv {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {d : ℕ} (θ : LevelCuspCharacters.Tor p d →* Kˣ)
    (z : LevelCuspCharacters.Fbar p) : LevelCuspCharacters.torVal θ⁻¹ z = LevelCuspCharacters.torVal θ z⁻¹ := by
  have hinj : Function.Injective
      (fun u : LevelCuspCharacters.Tor p d => ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p)) :=
    fun a b hab => Subtype.ext (Units.ext hab)
  unfold LevelCuspCharacters.torVal
  by_cases hz : ∃ u : LevelCuspCharacters.Tor p d, ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) = z
  · obtain ⟨u, rfl⟩ := hz
    have h2 : (((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p))⁻¹ =
        (((u⁻¹ : LevelCuspCharacters.Tor p d) : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) := by simp
    rw [h2, hinj.extend_apply, hinj.extend_apply]
    simp
  · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply']
    · rfl
    · rintro ⟨u, hu⟩
      exact hz ⟨u⁻¹, by simp [hu]⟩

theorem cuspChar_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)),
    h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  intro p _ K _ ι _ _ θ h h' hh
  classical
  have hh' : h' * h = 1 := mul_eq_one_comm.1 hh
  have key : ∀ (a b : Matrix ι ι (ZMod p)), a * b = 1 →
      Matrix.toLin' (a.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) *
        Matrix.toLin' (b.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) = 1 := by
    intro a b hab
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  have heig := eigenspace_inv _ _ (key h h' hh) (key h' h hh')
  have hmem : ∀ z : LevelCuspCharacters.Fbar p, z ∈ (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset ↔
      z⁻¹ ∈ (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset := by
    intro z
    rw [Multiset.mem_toFinset, Multiset.mem_toFinset, mem_aroots_iff, mem_aroots_iff, heig]
  have hcard : (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card =
      (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card :=
    Finset.card_bijective _ inv_involutive.bijective hmem
  unfold LevelCuspCharacters.cuspChar
  by_cases H : ∃ (φ : (ZMod p)[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n
  · rw [if_pos H, if_pos (powIrr_of_inv h h' hh H)]
    congr 1
    refine Finset.sum_bijective _ inv_involutive.bijective (by convert hmem) ?_
    intro z _
    rw [torVal_inv, heig]
    congr 2
    funext i
    congr 3
  · rw [if_neg H, if_neg (fun H' => H (powIrr_of_inv h' h hh' H'))]

end GlobalTheory.CuspInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodReduceAlongThetaToIntegersStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  first | exact @GlobalTheory.QLog.hasPeriod_reduce | exact GlobalTheory.QLog.hasPeriod_reduce | (intros; apply GlobalTheory.QLog.hasPeriod_reduce <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValSubstPoly
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst_poly : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B), (∀ j, constantCoeff (u j) = 0) → ∀ g : MvPolynomial τ Q, HasVal p z (subst (up Q u) (g : MvPowerSeries τ Q)) (MvPolynomial.eval (fun j => algebraMap B Q (E (u j))) g) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u hu g
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  induction g using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [MvPolynomial.coe_monomial, subst_monomial ha, MvPolynomial.eval_monomial]
    have hprod : α.prod (fun s n => (up Q u s) ^ n) = map (algebraMap B Q) (α.prod fun s n => (u s) ^ n) := by
      simp [up, Finsupp.prod, map_prod, map_pow]
    have hEp : E (α.prod fun s n => (u s) ^ n) = α.prod fun s n => (E (u s)) ^ n := by
      simp [Finsupp.prod, map_prod, map_pow]
    have hv := GlobalTheory.T.hasPAdicPowerSeriesValue_map_of_continuousEvaluation p B O Q θ hF σ z hz E hE (α.prod fun s n => (u s) ^ n)
    have hs := (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ 0 _ 0 hv).2.1 c
    rw [hprod]
    convert hs using 1
    · rw [MvPowerSeries.smul_eq_C_mul]; rfl
    · rw [hEp]; simp [Finsupp.prod, map_prod, map_pow]
  | add f g hf hg =>
    rw [MvPolynomial.coe_add, subst_add ha, map_add]
    exact (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ _ _ _ hf).1 hg

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitDirectionAdd
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma piFinset_range_succ_eq_Iic {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → ℕ) :
    Fintype.piFinset (fun i => Finset.range (κ i + 1)) = Finset.Iic κ := by
  ext μ
  simp [Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Iic, Pi.le_def, Nat.lt_succ_iff]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.jet_split_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) μ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have hμ := fun μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ =>
    ((_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ c t μ hk ha hτ).mul_left
      (((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i))))
  have hs := hasSum_sum (s := Finset.Iic κ) fun μ _ => hμ μ
  refine (_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ (c + v) t κ hk ha hτ).unique
    (hs.congr_fun fun ξ => ?_)
  simp_rw [_root_.GlobalTheory.HilbFam.lag_add, Finset.prod_univ_sum, piFinset_range_succ_eq_Iic,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirection
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem jet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ (v * c) (v * t) κ hk ha hτ
  have h2 := (GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ).mul_left (v ^ (∑ i, κ i))
  refine h1.unique (HasSum.congr_fun h2 fun ξ ↦ ?_)
  have hp : (∏ i : Emb F, lag k (κ i) (v * c) ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t))) =
      v ^ (∑ i, κ i) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [show (2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t) = v * ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) by ring]
    exact (lag_homogeneous k (κ i) c _ v).1
  rw [hp]; ring

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem point_hol_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  intro E _ _ W X hX x x' h
  have : IsSeparated (terminal.from X) := hX.isSeparated_terminal_from
  exact point_hol_ext E W X (⊤_ Scheme) (terminal.from X) x x' (terminal.hom_ext _ _) h

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicValueDerivativeL2BallStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_value_derivative_l2_ball : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ), DifferentiableOn ℂ u (ball p r) → ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤ ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  first | exact @GlobalTheory.l2_value_deriv_ball | exact GlobalTheory.l2_value_deriv_ball | (intros; apply GlobalTheory.l2_value_deriv_ball <;> assumption)
end

