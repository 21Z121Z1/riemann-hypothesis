import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0346
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteQuotientRestrictBijective

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonGaloisFixedStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_galois_fixed : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (y : (HSW r M j).M n), galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by
  first | exact @GlobalTheory.CompanionTheory.BWGal.bW_gal | exact GlobalTheory.CompanionTheory.BWGal.bW_gal | (intros; apply GlobalTheory.CompanionTheory.BWGal.bW_gal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonPullbackCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_pullback_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n), pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by
  first | exact @GlobalTheory.CompanionTheory.CrisBase.pullM_bW | exact GlobalTheory.CompanionTheory.CrisBase.pullM_bW | (intros; apply GlobalTheory.CompanionTheory.CrisBase.pullM_bW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonReductionCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)), (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) := by
  first | exact @GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | exact GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | (intros; apply GlobalTheory.CompanionTheory.CrisBaseChange.bW_red <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompatStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_level_morphism_cover_compat : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k) (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c)) (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory), stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj), (∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j)) → ∀ j, Function.Bijective (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoverGlue.glue | exact GlobalTheory.CompanionTheory.FlatCoverGlue.glue | (intros; apply GlobalTheory.CompanionTheory.FlatCoverGlue.glue <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteQuotientRestrictBijectiveStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_site_quotient_restrict_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resVq q ρ m 𝒱 c).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ZariskiStratumQuotient.main | exact GlobalTheory.CompanionTheory.ZariskiStratumQuotient.main | (intros; apply GlobalTheory.CompanionTheory.ZariskiStratumQuotient.main <;> assumption)
end

