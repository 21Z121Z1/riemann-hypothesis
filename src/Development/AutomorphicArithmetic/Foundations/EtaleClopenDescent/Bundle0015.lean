import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3671
import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0047
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopenSubgroupLocus
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsPIsogIsTjOfSectionRepData
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0065

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplexModelPointsOfGenericFiberEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

theorem UpperTheory.Cb.complexModel_points_of_genericFiber_embedding :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (φ : R →+* ℂ) (gb : GBase D.toG ℂ), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N) (j : X.X ⟶ pullback M.s (spMap φ)), IsOpenImmersion j → IsClosedImmersion j → j ≫ pullback.snd _ _ = X.s → IsGPull X.univ M.univ (j ≫ pullback.fst _ _) → ∀ y' : Sp ℂ ⟶ M.X, y' ≫ M.s = spMap φ → ∃! y : Sp ℂ ⟶ X.X, y ≫ X.s = 𝟙 _ ∧ y ≫ j ≫ pullback.fst _ _ = y' := by
  intro p _ D R _ _ b φ gb hρ ht N h3 hcop M X j hjo hjc hjs hg y' hy'
  obtain ⟨o₁, ⟨e₁⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp ℂ) M.s y' M.univ
  have hs : y' ≫ M.s = 𝟙 (Sp ℂ) ≫ spMap φ := by rw [hy', Category.id_comp]
  let og : GObj gb N (𝟙 (Sp ℂ)) := GenCmp.toGObj (GenCmp.rebase hρ ht hs o₁) (GenCmp.geomFull hcop _)
  obtain ⟨f, ⟨hf, ⟨g⟩⟩, -⟩ := X.rep (Sp ℂ) (𝟙 _) og
  let O₂ := GenCmp.toObj hρ ht X.univ (GenCmp.genericObject_kernelCondition _)
  have e2 : ObjMap o₁ O₂ f := ⟨g.φ, g.φ₂, g.cart, g.sq, g.act, g.pol, g.eta⟩
  obtain ⟨φA, φ₂, hc, hsq, ha, ⟨hp⟩, he⟩ := hg
  have e3 : ObjMap O₂ M.univ (j ≫ pullback.fst _ _) := ⟨φA, φ₂, hc, hsq, ha, hp, he⟩
  obtain ⟨e4⟩ := objMap_comp p D R b N (Sp ℂ) X.X M.X _ _ _ o₁ O₂ M.univ f _ e2 e3
  have hcomp : (f ≫ j ≫ pullback.fst M.s (spMap φ)) ≫ M.s = y' ≫ M.s := by
    rw [hy']
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc j, hjs, ← Category.assoc, hf, Category.id_comp]
  have hfy : f ≫ j ≫ pullback.fst M.s (spMap φ) = y' := by
    obtain ⟨f', -, hu⟩ := M.rep (Sp ℂ) (y' ≫ M.s) o₁
    exact (hu _ ⟨hcomp, ⟨e4⟩⟩).trans (hu y' ⟨rfl, ⟨e₁⟩⟩).symm
  refine ⟨f, ⟨hf, hfy⟩, fun y hy => ?_⟩
  apply (cancel_mono j).1
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hy.2, hfy]
  · simp only [Category.assoc]
    rw [hjs, hy.1, hf]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPIsogenyKernelEqSubgroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

namespace UpperTheory.QO

private theorem main' : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) [GrpObj K] (i : K ⟶ o.A), IsMonHom i → Mono i → IsFinite K.hom → Etale K.hom → (∀ (T : Over S) (x : T ⟶ o.A), InSub i x → KilledBy o w x) → (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) → IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) → ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ _ b N h3 hcop hp hm r w j c hw hle hj hc S _ s o K _ i hi hmono hfin het hkill hstab hdeg
  obtain ⟨Y, o₀, m₀, o', ψ, hYf, hYe, his, htj, hu⟩ :=
    GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable p D R b N h3 hcop hp r w j c hw hle hj hc hm S s o
  let Rd : RepData b N r w j c s o := ⟨Y, o₀, m₀, o', ψ, hYf, hYe, his, htj, hu⟩
  let Sd : SubData w j o := ⟨K, i, hi, hmono, hfin, het, hkill, hstab, hdeg⟩
  obtain ⟨W, hWo, hWc, hWat, hWgeo⟩ := UpperTheory.exists_clopen_subgroup_locus p D R b N r w j c hp hw hle hc S s o Rd Sd
  have hex : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      ∃ y, y ≫ Rd.Y.hom = x ∧ Set.range y ⊆ W := by
    intro k _ _ x
    obtain ⟨y, hy, hg⟩ := UpperTheory.repData_geometric_points_of_subData p D R b N h3 hcop hp hm r w j c hw hle hj hc S s o Rd Sd k x
    exact ⟨y, hy, (hWgeo k y).2 hg⟩
  have huq : ∀ (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Rd.Y.left),
      y₁ ≫ Rd.Y.hom = y₂ ≫ Rd.Y.hom → Set.range y₁ ⊆ W → Set.range y₂ ⊆ W → y₁ = y₂ := by
    intro k _ _ y₁ y₂ h h₁ h₂
    exact UpperTheory.subData_points_correspond_repData p D R b N h3 hcop hp hm r w j c hw hle hc S s o Rd Sd k y₁ y₂ h
      ((hWgeo k y₁).1 h₁) ((hWgeo k y₂).1 h₂)
  obtain ⟨σ, hσ, hσW⟩ := UpperTheory.exists_section_of_etale_clopen_geomPoint_unique S Rd.Y Rd.fin Rd.et W hWo hWc hex huq
  obtain ⟨o'', ψ'', h1, h2, h3'⟩ := UpperTheory.exists_isPIsog_isTj_of_section_repData p D R b N h3 hcop r w j c S s o Rd σ hσ
  refine ⟨o'', ψ'', h1, h2, fun T a => ?_⟩
  obtain ⟨a₀, ha₀, hψ, hk⟩ := h3' T a
  have key := hWat S σ hσW T T.hom a₀ a ha₀
  rw [hψ]
  simp only [hk]
  exact key

end UpperTheory.QO

theorem UpperTheory.Cb.exists_pIsogeny_kernel_eq_subgroupScheme :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∀ (o : Obj b N s) (K : Over S) [GrpObj K] (i : K ⟶ o.A), IsMonHom i → Mono i → IsFinite K.hom → Etale K.hom → (∀ (T : Over S) (x : T ⟶ o.A), InSub i x → KilledBy o w x) → (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) → IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) → ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ b N hN hNp hm r w j c hw hu hj hc S _ s hp o K _ i hi hmono hKf hKe hkill hst hdeg
  obtain ⟨R₁, _, _, b₁, s₁, hp₁, L⟩ := UpperTheory.exists_noetherian_base_link p D R b S s hp
  obtain ⟨o', ψ, h1, h2, h3⟩ := UpperTheory.QO.main' p D R₁ b₁ N hN hNp hp₁ hm r w j c hw hu hj hc S s₁
    (UpperTheory.QO.conv L o) K i hi hmono hKf hKe hkill hst hdeg
  exact ⟨UpperTheory.QO.conv L.symm o', ψ, h1, h2, h3⟩
end

