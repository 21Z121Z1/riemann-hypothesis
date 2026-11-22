import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateFromSandwich
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoLow
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem ontoLow_h_basis (P : HTPre l K) (N : Model l K) (a n : ℕ) (v : N.V n) {m : ℕ}
    (b : Module.Basis (Fin m) K (Hdg N.q a n)) (φ : Module.Dual K (Hdg N.q a n)) :
    P.h N a n v φ = ∑ t, kC K (φ (b t)) * P.h N a n v (b.coord t) := by
  conv_lhs => rw [← b.sum_dual_apply_smul_coord φ]
  rw [map_sum]
  exact Finset.sum_congr rfl fun t _ => P.lin' N a n (φ (b t)) v (b.coord t)

theorem ontoLow_genMap_comp (M N : Model l K) (p : N.X ⟶ M.X) (s : M.X ⟶ N.X) (hp : p ≫ M.p = N.p)
    (hs : s ≫ N.p = M.p) (hsp : s ≫ p = 𝟙 _) : Model.genMap s hs ≫ Model.genMap p hp = 𝟙 M.gen := by
  apply pullback.hom_ext
  · simp only [Model.genMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    rw [hsp, Category.comp_id]
  · simp only [Model.genMap, Category.assoc, pullback.lift_snd, Category.id_comp]

theorem ontoLow_pf : OntoLow := by
  intro hcup hret hon l _ K _ P hinj M d hM hd n
  obtain ⟨N, p, s, hp, hsp, hN, hNd⟩ := hret l K M d hM hd
  have hs : s ≫ N.p = M.p := by rw [← hp, ← Category.assoc, hsp, Category.id_comp]
  have hSN : Surj P N n := hon l K P N (d + 1) (by omega) hN hNd (hinj N hN _) n
  intro m b z hz a ha
  have : ∀ a, FiniteDimensional K (Hdg N.q a n) := fun a => (P.fin N hN a n).1
  let b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg N.q a n))) K (Hdg N.q a n) := fun a => Module.finBasis K _
  let S : ∀ a, Hdg N.q a n →ₗ[K] Hdg M.q a n := fun a => pullH (Model.genMap s hs) (Model.genMap_q s hs) a n
  let z' : ∀ a, Fin (Module.finrank K (Hdg N.q a n)) → ℂ_[l] :=
    fun a t => ∑ s', z a s' * kC K ((b a).coord s' (S a (b' a t)))
  have hz' : ∀ a ≤ n, z' a = 0 := hSN b' z' (by
    intro v
    refine Eq.trans ?_ (hz (Model.pullV s hs n v))
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [z', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [P.nat M N s hs hM hN, ontoLow_h_basis P N a n v (b' a), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [LinearMap.comp_apply, S]
    ring)
  have key : ∀ x, ∑ s', z a s' * kC K ((b a).coord s' (S a x)) = 0 := by
    intro x
    rw [← (b' a).sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    have h0 := congrFun (hz' a ha) t
    simp only [z', Pi.zero_apply] at h0
    have e : ∀ s', z a s' * (kC K ((b' a).repr x t) * kC K ((b a).coord s' (S a (b' a t)))) =
        kC K ((b' a).repr x t) * (z a s' * kC K ((b a).coord s' (S a (b' a t)))) := fun _ => by ring
    simp_rw [e, ← Finset.mul_sum, h0, mul_zero]
  have hsurj : ∀ y, S a (pullH (Model.genMap p hp) (Model.genMap_q p hp) a n y) = y := by
    intro y
    have h1 := (hcup K M.gen M.q).2.2.2.2.2.2 N.gen M.gen N.q M.q (Model.genMap p hp) (Model.genMap_q p hp)
      (Model.genMap s hs) (Model.genMap_q s hs) (𝟙 M.gen) (Category.id_comp M.q)
      (ontoLow_genMap_comp M N p s hp hs hsp) a n y
    rw [(hcup K M.gen M.q).2.2.2.2.2.1 a n y] at h1
    exact h1
  funext s₀
  have := key (pullH (Model.genMap p hp) (Model.genMap_q p hp) a n ((b a) s₀))
  rw [hsurj] at this
  simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] using this

end CrystallineSemistableComparison.Onto

end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.Retract
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap IsProjOver)

def retractPt (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    Spec (CommRingCat.of (OK l K)) ⟶ PSpace (OK l K) 2 :=
  GlobalTheory.ProjSpace.pt (RingHom.id (OK l K)) (fun _ => 1)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one)

theorem retractPt_str (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    retractPt l K ≫ PSpace.str (OK l K) 2 = 𝟙 _ := by
  rw [retractPt, GlobalTheory.ProjSpace.pt_str]
  simp [spMap]

theorem retract_pf : Retract := by
  intro l _ K _ M d hM hd
  let N : Model l K := ⟨pullback M.p (PSpace.str (OK l K) 2), pullback.fst _ _ ≫ M.p⟩
  have h2 : SmoothOfRelativeDimension 2 (pullback.fst M.p (PSpace.str (OK l K) 2)) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 2)
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 2) _ _
      (GlobalTheory.Adelic.smoothOfRelativeDimension_pspace _ 2)
  have hN : SmoothOfRelativeDimension (d + 1 + 1) N.p := by
    have := h2
    have := hd
    have : SmoothOfRelativeDimension (2 + d) (pullback.fst M.p (PSpace.str (OK l K) 2) ≫ M.p) :=
      smoothOfRelativeDimension_comp 2 d _ _
    rw [show d + 1 + 1 = 2 + d by omega]
    exact this
  have hsm : Smooth N.p := SmoothOfRelativeDimension.smooth (d + 1 + 1) N.p
  obtain ⟨⟨hproj, ϖ, hϖ, -⟩, -⟩ := hM
  refine ⟨N, pullback.fst _ _, pullback.lift (𝟙 _) (M.p ≫ retractPt l K) ?_, rfl, pullback.lift_fst _ _ _,
    ⟨⟨?_, ϖ, hϖ, ?_⟩, hsm⟩, hN⟩
  · rw [Category.assoc, retractPt_str, Category.comp_id, Category.id_comp]
  · exact GlobalTheory.ProjSpace.isProjOver_pullback hproj (GlobalTheory.ProjSpace.isProjOver_pspace_str _ 2)
  · intro x
    exact GlobalTheory.T.hasStrictlySemistableChartAt_of_smooth _ ϖ N.X N.p ⊤ x trivial inferInstance

end CrystallineSemistableComparison.Onto

end
end

