import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.CubeIso

section

variable {X X₁ X₂ Y : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

theorem mem_ext {x : X} {j₁ : L₁.ι} {j₂ : L₂.ι} (h₁ : f₁ x ∈ L₁.U j₁) (h₂ : f₂ x ∈ L₂.U j₂) :
    x ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) :=
  ⟨mem_pull.2 h₁, mem_pull.2 h₂⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂') :
    gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
        (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂'))
      ((extLB L₁ L₂ f₁ f₂).g (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂')) =
      gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') * gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') := by
  have hm : r z ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
      (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂') := ⟨mem_ext h₁ h₂, mem_ext h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hm _).trans ?_) ((gm_res r z _ hm _).trans ?_))
  · exact gm_pull_g L₁ f₁ r z (fun _ => j₁) (fun _ => j₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g L₂ f₂ r z (fun _ => j₂) (fun _ => j₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

def ev (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι) (k : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓ L.U k)
    (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k))

theorem ev_trans {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z)
    (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι) (k k' : L.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂')
    (h : r z ∈ L.U k) (h' : r z ∈ L.U k') :
    ev w r z j₁ j₂ k = gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') *
      gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') * (gm r z (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        ev w r z j₁' j₂' k' := by
  rw [← gm_ext_g r z j₁ j₁' j₂ j₂' h₁ h₁' h₂ h₂']
  exact AdjComp.gm_iso hw r z (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂', k')
    ⟨mem_ext h₁ h₂, h⟩ ⟨mem_ext h₁' h₂', h'⟩

theorem exists_linComb (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (w₀ : LB.Iso L (extLB L₁ L₂ f₁ f₂))
    (hw₀ : w₀.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ₁ : K → (Y ⟶ X₁)) (ε : K → ℤ) (σ : K → K)
    (h₁ : ∀ k, φ k ≫ f₁ = φ₁ k) (h₂ : ∀ k, φ k ≫ f₂ = φ (σ k) ≫ f₂)
    (hε : ∀ (G : Type) [CommGroup G] (a : K → G), (∀ k, a k = a (σ k)) → ∏ k, a k ^ ε k = 1) :
    ∃ w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L₁ φ₁ ε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (jC : K → L₁.ι) (jA : K → L.ι) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ φ₁ jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) →
        gm f z (LB.wchart L₁ φ₁ jC ⊓ LB.wchart L φ jA) (w.s (jC, jA)) =
          ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
  obtain rfl : (fun k => φ k ≫ f₁) = φ₁ := funext h₁
  have cover : ∀ y : Y, ∃ β : K → L₂.ι, (∀ k, f₂ (φ k y) ∈ L₂.U (β k)) ∧ ∀ k, β k = β (σ k) := fun y => by
    choose c hc using exists_chart hL₂
    exact ⟨fun k => c ((φ k ≫ f₂) y), fun k => hc _, fun k => congrArg (fun q : Y ⟶ X₂ => c (q y)) (h₂ k)⟩
  have glue : ∀ (jC : K → L₁.ι) (jA : K → L.ι),
      ∃ s : Γ(Y, LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ (fun k => φ k ≫ f₁) jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) → gm f z _ s = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
    intro jC jA
    let W : {β : K → L₂.ι // ∀ k, β k = β (σ k)} → Y.Opens := fun β =>
      LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA ⊓ LB.wchart L₂ (fun k => φ k ≫ f₂) β.1
    have l₀ : ∀ β, W β ≤ LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA := fun β => inf_le_left
    have l₁ : ∀ β k, W β ≤ φ k ⁻¹ᵁ
        ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k)) ⊓ L.U (jA k)) := fun β k y hy =>
      ⟨mem_ext (Set.mem_iInter.1 hy.1.1 k) (Set.mem_iInter.1 hy.2 k), Set.mem_iInter.1 hy.1.2 k⟩
    let u : ∀ β, Γ(Y, W β)ˣ := fun β => ∏ k, res (l₁ β k)
      (pullU (φ k) _ (w₀.s (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k), jA k))) ^ ε k
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) β (hz : f z ∈ W β),
        gm f z (W β) (u β) = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β.1 k) (jA k) ^ ε k := fun Z f z β hz =>
      (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res f z (l₁ β k) hz _).trans (gm_pull f (φ k) z _ (l₁ β k hz) _))))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun y hy => by
        obtain ⟨β, hβ, hβ'⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨β, hβ'⟩, hy, Set.mem_iInter.2 hβ⟩) u (fun β β' y hy => by
        rw [hu _ (𝟙 Y) y β hy.1, hu _ (𝟙 Y) y β' hy.2]
        have a : ∀ k, ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β.1 k) (jA k) =
            gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k)) *
              ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β'.1 k) (jA k) := fun k => by
          have m₁ : f₁ (φ k y) ∈ L₁.U (jC k) := Set.mem_iInter.1 hy.1.1.1 k
          have m : φ k y ∈ L.U (jA k) := Set.mem_iInter.1 hy.1.1.2 k
          rw [Category.id_comp, ev_trans hw₀ (φ k) y (jC k) (jC k) (β.1 k) (β'.1 k) (jA k) (jA k) m₁ m₁
            (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k) m m, gm_self hL₁ (φ k ≫ f₁) y m₁,
            gm_self hL (φ k) y m, _root_.one_mul, inv_one, _root_.mul_one]
        simp only [a, mul_zpow, Finset.prod_mul_distrib]
        rw [hε _ (fun k => gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k))) (fun k => by
          have key : ∀ (q q' : Y ⟶ X₂) (i i' j j' : L₂.ι), q = q' → i = i' → j = j' →
              gm q y (L₂.U i ⊓ L₂.U j) (L₂.g i j) = gm q' y (L₂.U i' ⊓ L₂.U j') (L₂.g i' j') := by
            rintro _ _ _ _ _ _ rfl rfl rfl; rfl
          exact key _ _ _ _ _ _ (h₂ k) (β.2 k) (β'.2 k)), _root_.one_mul])
    refine ⟨s, fun Z f z β hC hA hβ hβ' => ?_⟩
    have hy : f z ∈ W ⟨β, hβ'⟩ := ⟨⟨hC, hA⟩, Set.mem_iInter.2 hβ⟩
    exact (gm_res f z (l₀ ⟨β, hβ'⟩) hy s).symm.trans
      ((congrArg (gm f z (W ⟨β, hβ'⟩)) (hs ⟨β, hβ'⟩)).trans (hu Z f z ⟨β, hβ'⟩ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun i j => unit_ext fun y hy => ?_,
    fun Z f z jC jA β hC hA hβ hβ' => hs jC jA Z f z β hC hA hβ hβ'⟩
  obtain ⟨β, hβ, hβ'⟩ := cover y
  have e₁ := hs i.1 i.2 _ (𝟙 Y) y β hy.1.1 hy.1.2 hβ hβ'
  have e₂ := hs j.1 j.2 _ (𝟙 Y) y β hy.2.1 hy.2.2 hβ hβ'
  have gC := gm_linComb L₁ (fun k => φ k ≫ f₁) ε (𝟙 Y) y i.1 j.1 hy.1.1 hy.2.1
  have gA := gm_linComb L φ ε (𝟙 Y) y i.2 j.2 hy.1.2 hy.2.2
  refine (gm_res (𝟙 Y) y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) ((gm_div (LB.LinComb L φ ε) (LB.LinComb L₁ (fun k => φ k ≫ f₁) ε) (𝟙 Y) y i j hy).trans
    (congrArg₂ (fun a b => a * b⁻¹) gC gA)) ((gm_res (𝟙 Y) y _ hy _).trans e₂)).trans ?_
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Category.id_comp]
  rw [ev_trans hw₀ (φ k) y (i.1 k) (j.1 k) (β k) (β k) (i.2 k) (j.2 k) (Set.mem_iInter.1 hy.1.1 k)
    (Set.mem_iInter.1 hy.2.1 k) (hβ k) (hβ k) (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k),
    gm_self hL₂ (φ k ≫ f₂) y (hβ k), _root_.mul_one, mul_zpow, mul_zpow, inv_zpow]

end

theorem cancel_two (G : Type) [CommGroup G] (a : ULift.{0} (Finset (Fin 2)) → G)
    (h : ∀ I, a I = a ⟨insert 0 I.down⟩) : ∏ I, a I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  rw [← Equiv.prod_comp (Equiv.ulift.{0}.symm : Finset (Fin 2) ≃ ULift.{0} (Finset (Fin 2)))]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e₀ : a ⟨∅⟩ = a ⟨{0}⟩ := h ⟨∅⟩
  have e₁ : a ⟨{1}⟩ = a ⟨{0, 1}⟩ := h ⟨{1}⟩
  show a ⟨∅⟩ ^ (1 : ℤ) * (a ⟨{0}⟩ ^ (-1 : ℤ) * (a ⟨{1}⟩ ^ (-1 : ℤ) * a ⟨{0, 1}⟩ ^ (1 : ℤ))) = 1
  rw [e₀, e₁]
  simp

end GlobalTheory.MumProd.CubeIso

namespace GlobalTheory.MumProd

theorem exists_cubeIso : ∀ (S : Scheme.{0}) (B B₁ B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B₂] [IsCommMonObj B₂] (M : LB B.left) (M₁ : LB B₁.left) (M₂ : LB B₂.left), M.IsLB → M₁.IsLB → M₂.IsLB → ∀ (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (wM : LB.Iso M (extLB M₁ M₂ p₁.left p₂.left)), wM.IsGen → ∀ (x : Fin 2 → (T ⟶ B)) (x₁ : Fin 2 → (T ⟶ B₁)), (∀ I : Finset (Fin 2), psum B x I ≫ p₁ = psum B₁ x₁ I) → (∀ I : Finset (Fin 2), psum B x I ≫ p₂ = psum B x (insert 0 I) ≫ p₂) → ∃ w : LB.Iso (cubeLB B x M) (cubeLB B₁ x₁ M₁), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ T.left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → M₁.ι) (jA : ULift.{0} (Finset (Fin 2)) → M.ι) (β : ULift.{0} (Finset (Fin 2)) → M₂.ι), f z ∈ (cubeLB B₁ x₁ M₁).U jC → f z ∈ (cubeLB B x M).U jA → (∀ I, (f ≫ (psum B x I.down).left ≫ p₂.left) z ∈ M₂.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum B x I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  intro S B B₁ B₂ T _ _ _ _ _ _ M M₁ M₂ hM hM₁ hM₂ p₁ p₂ wM hwM x x₁ h₁ h₂
  obtain ⟨w, hw, H⟩ := CubeIso.exists_linComb hM hM₁ hM₂ wM hwM (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B x I.down).left) (fun I => (psum B₁ x₁ I.down).left) (fun I => (-1) ^ (2 - I.down.card))
    (fun I => ⟨insert 0 I.down⟩) (fun I => by rw [← Over.comp_left, h₁])
    (fun I => by rw [← Over.comp_left, ← Over.comp_left, h₂]) CubeIso.cancel_two
  exact ⟨w, hw, fun Z f z jC jA β hC hA hβ hβ' => H Z f z jC jA β hC hA hβ hβ'⟩

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.FactorAdj

open AdjComp

def chartPullTwo {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y'' ⟶ X)) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Y'' ⟶ Y') (n : Y' ⟶ Y) (hc : ∀ k, φ' k = (h ≫ n) ≫ φ k) :
    ChartPull (LB.LinComb L φ' ε) ((LB.LinComb L φ ε).pull n) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ ((LB.LinComb L φ ε).pull n).U (fun _ => j) := fun j _ hy =>
    (mem_pull (L := LB.LinComb L φ ε)).2 ((chartPullSame L φ' φ ε (h ≫ n) hc).le j hy)
  { idx := fun j _ => j
    le := le
    g := fun y j j' hj hj' => ((chartPullSame L φ' φ ε (h ≫ n) hc).g y j j' hj hj').trans
      (gm_pull_g (LB.LinComb L φ ε) n h y (fun _ => j) (fun _ => j') (le j hj) (le j' hj')).symm }

theorem exists_pull_lam {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} {n : G2 G ⟶ G2 G'} (w : LB.Iso (abelian₂ G L) ((abelian₂ G' L').pull n.left))
    (hw : w.IsGen) (m : T ⟶ G2 G) (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T ⟶ G')) (hx : ∀ i, x i = m ≫ x2 G i)
    (hx' : ∀ i, x' i = (m ≫ n) ≫ x2 G' i) :
    ∃ w' : LB.Iso (cubeLB G x L) (cubeLB G' x' L'), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ T.left) (z : Z) J' J,
      Good L' z J' → Good L z J → adjVal w' p z J' J = lamVal w (p ≫ m.left) z J' J := by
  let a : ChartPull (cubeLB G x L) (abelian₂ G L) m.left := cubePull L m _ _ hx
  let b : ChartPull (cubeLB G' x' L') ((abelian₂ G' L').pull n.left) m.left :=
    chartPullTwo L' _ _ _ m.left n.left (psum_left_pull (m ≫ n) _ _ hx')
  refine ⟨pullIso a b w, pullIso_isGen a b hw, fun Z p z J' J hJ' hJ => ?_⟩
  have mA := Good.mem hJ (fun I : ULift (Finset (Fin 2)) => (psum G x I.down).left) p
  have mB := Good.mem hJ' (fun I : ULift (Finset (Fin 2)) => (psum G' x' I.down).left) p
  refine ((adjVal_of (pullIso a b w) p z J' J _ _ (fun _ => rfl) (fun _ => rfl)).trans
    (gm_pullIso a b w p z (_, _) ⟨mB, mA⟩)).trans ?_
  have e₁ : (fun I : ULift (Finset (Fin 2)) => J (p ≫ (psum G x I.down).left)) =
      fun I => J ((p ≫ m.left) ≫ (psum G (x2 G) I.down).left) := funext fun I => by
    rw [psum_left_pull m _ _ hx I, Category.assoc]
  have e₂ : (fun I : ULift (Finset (Fin 2)) => J' (p ≫ (psum G' x' I.down).left)) =
      fun I => J' ((p ≫ m.left) ≫ n.left ≫ (psum G' (x2 G') I.down).left) := funext fun I => by
    rw [psum_left_pull (m ≫ n) _ _ hx' I, Over.comp_left, Category.assoc, Category.assoc]
  rw [e₁, e₂]
  rfl

theorem exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribMulAction.toAddMonoidHom D'.toPre.X F.e) y) (((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D' F
  let m : (pol D').B ⊗ (pol D).B ⟶ G2 (pol D).B := lift (fst _ _ ≫ F.pr) (snd _ _)
  let n : G2 (pol D).B ⟶ G2 (pol D').B := lift (fst _ _ ≫ F.inc) (snd _ _ ≫ F.inc ≫ F.o.onB.act F.f)
  let w₀ : LB.Iso (abelian₂ (pol D).B (pol D).M.L) ((abelian₂ (pol D').B (pol D').M.L).pull n.left) := F.w
  obtain ⟨w, gw, hw⟩ := exists_pull_lam w₀ F.w_gen m ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B]
    ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f]
    (fun i => by
      fin_cases i
      · exact (lift_fst _ _).symm
      · exact (lift_snd _ _).symm)
    (fun i => by
      fin_cases i
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_fst _ _)).trans ?_))
        refine (lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
        exact congrArg (fst (pol D').B (pol D).B ≫ ·) F.pr_inc
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_snd _ _)).trans ?_))
        exact lift_snd_assoc _ _ _)
  refine ⟨w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hP : (lift (toUnit (TK R) ≫ D.toPre.c (F.xp y)) (toUnit (TK R) ≫ D.toPre.c y')).left =
      (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left ≫ m.left := by
    refine congrArg (fun q : TK R ⟶ G2 (pol D).B => q.left) (Eq.symm ((comp_lift _ _ _).trans ?_))
    refine congrArg₂ lift ((lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)) (lift_snd _ _)
    exact congrArg (toUnit (TK R) ≫ ·) (c_xp F y).symm
  have e := F.tau (F.xp y) y' z J₁ J₂ hJ₁ hJ₂
  rw [F.xi_xp, hP] at e
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre _ _).choose_spec.2 _ _ z J₂ hJ₂).trans (e.trans ?_)
  exact congrArg₂ (· * ·) (hw _ _ z J₁ J₂ hJ₁ hJ₂).symm
    ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre (F.e • y) (F.f • F.xi y')).choose_spec.2 _ _ z J₁ hJ₁).symm

end GlobalTheory.MumFam.FactorAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationValuesAlgClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationValues_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∃ N : NumD F, Nonempty (NumOf D.toPre F N) := by
  first | exact @GlobalTheory.MumValues.exists_values | exact GlobalTheory.MumValues.exists_values | (intros; apply GlobalTheory.MumValues.exists_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedLineBundleEquivariantGenerator
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CharKer

theorem pmap_eq_whiskerRight {S : Scheme.{0}} {A A' : Over S} (q : A ⟶ A') (T : Over S) : pmap q T = q ▷ T := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]

theorem isPullback_over_left {S : Scheme.{0}} {P X Y Z : Over S} {f : P ⟶ X} {g : P ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
    (H : IsPullback f g h k) : IsPullback f.left g.left h.left k.left :=
  H.map (Over.forget S)

theorem res_res_units {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  change _ = (X.presheaf.map ((homOfLE h₁).op ≫ (homOfLE h₂).op)).hom x.val
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]; rfl

theorem res_pullU_units {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  apply Units.ext
  have := f.naturality (homOfLE h).op
  change (X.presheaf.map (homOfLE h).op ≫ f.app V).hom x.val = _
  rw [this]; rfl

theorem mul_mul_inv_mul_inv_cancel {G : Type*} [CommGroup G] (c x y : G) : (c * x) * (c * y)⁻¹ = x * y⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]

theorem exists_equivGen : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∃ (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), M.IsLB ∧ IsEquivGen i q χ M e := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hker hχ
  have hloc := GlobalTheory.T.exists_nhds_characterUnit_kernel_action S A A' N T i q χ hi hq hfin hflat hsurj hker hχ
  have : Flat (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : Surjective (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : QuasiCompact (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have hpb : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    isPullback_over_left (GlobalTheory.T.kernelAction_isPullback_prodMap_torsor S A A' N T i q hi hq hker)
  have hw : ∀ z, (pmap q T).left ((actMap i T).left z) = (pmap q T).left ((prMap A N T).left z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have inj : ∀ U : (A' ⊗ T).left.Opens, Function.Injective (pullU (pmap q T).left U) := fun U x y hxy =>
    Units.ext (ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj (pmap q T).left U (congrArg Units.val hxy))
  have desc : ∀ (U : (A' ⊗ T).left.Opens) (u : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ U)ˣ),
      (∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U))
        (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U)),
        res h₁ (pullU (actMap i T).left _ u) = res h₂ (pullU (prMap A N T).left _ u)) →
      ∃ g : Γ((A' ⊗ T).left, U)ˣ, pullU (pmap q T).left U g = u := by
    intro U u hu
    have hg : (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) :=
      fun z hz => show (pmap q T).left ((actMap i T).left z) ∈ U from (hw z) ▸ hz
    have key := GlobalTheory.FlatDescent.existsUnique_app_eq_iff (pmap q T).left hpb U _ rfl le_rfl hg u.val
    obtain ⟨a, ha, -⟩ := key.2 (congrArg Units.val (hu _ hg le_rfl)).symm
    obtain ⟨a, rfl⟩ := (GlobalTheory.FlatDescent.isUnit_app_iff (pmap q T).left U a).1 (ha ▸ u.isUnit)
    exact ⟨a, Units.ext ha⟩
  choose V hyV e he using hloc
  have hu : ∀ k l, ∃ g : Γ((A' ⊗ T).left, V k ⊓ V l)ˣ, pullU (pmap q T).left _ g =
      res ((pmap q T).left.preimage_mono inf_le_left) (e k) *
        (res ((pmap q T).left.preimage_mono inf_le_right) (e l))⁻¹ := fun k l => desc _ _ (by
    intro W h₁ h₂
    simp only [map_mul, map_inv, res_pullU_units, res_res_units]
    rw [he k W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_left))),
      he l W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_right))),
      mul_mul_inv_mul_inv_cancel])
  choose g hg using hu
  refine ⟨⟨(A' ⊗ T).left, V, g⟩, e, ⟨?_, ?_, ?_⟩, ?_, fun k W h₁ h₂ => he k W h₁ h₂⟩
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV y⟩
  · intro k
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, map_one, mul_inv_cancel]
  · intro a b c
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel_left]
  · intro k l W h₁ h₂ h₃
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogenyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  first | exact @GlobalTheory.DescNorm.descentDatum_of_additive | exact GlobalTheory.DescNorm.descentDatum_of_additive | (intros; apply GlobalTheory.DescNorm.descentDatum_of_additive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalStabiliserMulMemBigCellInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac

theorem exists_diag_mul_bigCell : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) :=
  GlobalTheory.T.inertPlace_bigCell_stabiliser_of_localRingBigCell_lemma GlobalTheory.T.exists_admissible_isUnit_det_local_involution

end GlobalTheory.DblVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameAlongArcFlagSpaceChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

namespace GlobalTheory.CompHS.ArcBridge

theorem arc_bridge : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι), W ≤ (L₀ TF.X Z la).U i → ∀ (ψ : ℂ → (Γ(Y₀ TF.X Z, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ bd₀ TF.X Z) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) → ∃ (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (fr : EigFrame TF.Y φ (x ≫ genι TF.Y)) (y : ℂ → FrPt Xo c (CAt σ)), IsBdArc TF.Y σ φ x ψ r ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) ∧ ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (u : ℂ), u ∈ Metric.ball (0 : ℂ) r → u ≠ 0 → ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 (y u)) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ hσ W hW i hWi ψ r hψ hs hin hout
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)
  let φ : c.F →+* Γ(Y₀ TF.X Z, W) := φ'.hom
  have hφ : (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ := hφ'.symm
  have hxc : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z ≫ TF.X.π) ≫ TF.Y.s = spMap φ ≫ spMap (RingHom.id c.F) := by
    have hid : spMap (RingHom.id c.F) = 𝟙 _ := by unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [hid, Category.comp_id, ← hφ]
    simp only [Category.assoc]
  let x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y := pullback.lift _ _ hxc
  have hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y := by
    rw [Category.assoc]; exact (pullback.lift_fst _ _ _).symm
  have hxs : x ≫ genStr TF.Y = spMap φ := pullback.lift_snd _ _ _
  have hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit) := fun s _ => by
    have h1 : (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) s ∈ W := hW.range_fromSpec.le ⟨s, rfl⟩
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.1 (hWi h1)
  obtain ⟨fr, hfr⟩ := GlobalTheory.T.exists_eigenFrame_chartVectors_compactFlagSpace_affine TF Z W hW φ hφ (i PUnit.unit) hz _ hx
  have hφu : ∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp φ = σ := fun u hu => by
    have h1 := hs u hu
    rw [hφ, spMap_comp'] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have key : ∀ (u : ℂ) (s : Sp ℂ), (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ U₀ TF.X Z ↔ (spMap (ψ u) ≫ x) s ∉ genBd TF.Y := by
    intro u s
    haveI := GlobalTheory.LogKS.isIso_fst TF.Y
    have e : (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ U₀ TF.X Z ↔ genι TF.Y ((spMap (ψ u) ≫ x) s) ∈ Set.range TF.Y.j := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hx]
      exact Iff.rfl
    rw [e, mem_genBd, not_not]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (genι TF.Y).isOpenEmbedding.injective (by rw [← ha]; rfl)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; rfl⟩
  have hb : IsBdArc TF.Y σ φ x ψ r := ⟨⟨hψ, hxs, hφu⟩, fun s => by
      have := hin s
      by_contra h
      exact this ((key 0 s).2 h), fun u hu h s => (key u s).1 (hout u hu h (Set.mem_univ s))⟩
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) r ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y :=
    fun u hu => GlobalTheory.ShFam.BdArc.exists_matches E H Dw l Xo c c.F (RingHom.id c.F) TF.Y σ _ φ x fr (ψ u) hxs
      (hφu u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r ∧ ((r / 2 : ℝ) : ℂ) ≠ 0 := by
    have := hψ.1
    refine ⟨?_, by exact_mod_cast (half_pos this).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos this).le]
    exact half_lt_self this
  haveI : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! yy hyy using hy'
  refine ⟨φ, x, fr, yy, hb, fun u hu h => hyy u ⟨hu, h⟩, fun g u hu h hO hi => ?_⟩
  exact GlobalTheory.T.value_weightSection_flagSpace_eq_rule_at_framedPoint TF Z la σ W hW i φ x hx hz fr hfr (ψ u) (yy u) (hφu u hu) (hyy u ⟨hu, h⟩) g hO hi

end GlobalTheory.CompHS.ArcBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerMatrixActionThetaCompactificati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.Sep.exists_isAct : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ act, IsAct X₁ act := by
  intro g n F W Z i X₁
  obtain ⟨c, hc, pr, h1, h2, h3⟩ := X₁.sharp
  choose act hact using fun a : Matrix (Fin 8) (Fin 8) ℤ =>
    (h2 X₁.ρ.P.A fun u => (List.ofFn fun v => pr v ^ a u v).prod).exists
  exact ⟨act, c, hc, pr, h1, h2, h3, hact⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndomorphismOfLatticePreservingLinearStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endomorphism_of_lattice_preserving_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : A ⟶ A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f := by
  first | exact @GlobalTheory.UnifEndo.exists_isMonHom_of_map_lattice | exact GlobalTheory.UnifEndo.exists_isMonHom_of_map_lattice | (intros; apply GlobalTheory.UnifEndo.exists_isMonHom_of_map_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_globalOneForms_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  first | exact @GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | exact GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | (intros; apply GlobalTheory.AbCoh.exists_equiv_globForm_baseChange <;> assumption)
end

