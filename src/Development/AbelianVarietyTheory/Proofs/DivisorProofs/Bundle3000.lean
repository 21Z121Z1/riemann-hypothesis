import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.SymAtOfThList
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.LamBridge

section Charts

variable {X X' Y : Scheme.{0}}

def cpTrans {A'' A' A : LB Y} (c₁ : ChartPull A'' A' (𝟙 Y)) (c₂ : ChartPull A' A (𝟙 Y)) : ChartPull A'' A (𝟙 Y) where
  idx i := c₂.idx (c₁.idx i)
  le i _ hy := c₂.le _ (c₁.le i hy)
  g y i j hi hj := (c₁.g y i j hi hj).trans (c₂.g y _ _ (c₁.le i hi) (c₁.le j hj))

def cpDiv {A' A B' B : LB Y} (a : ChartPull A' A (𝟙 Y)) (b : ChartPull B' B (𝟙 Y)) :
    ChartPull (LB.div B' A') (LB.div B A) (𝟙 Y) where
  idx p := (b.idx p.1, a.idx p.2)
  le p _ hy := ⟨b.le _ hy.1, a.le _ hy.2⟩
  g y p q hp hq := (gm_div A' B' (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans (by rw [a.g y _ _ hp.2 hq.2, b.g y _ _ hp.1 hq.1])
    (gm_div A B (𝟙 Y) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2)
      ⟨⟨b.le _ hp.1, a.le _ hp.2⟩, ⟨b.le _ hq.1, a.le _ hq.2⟩⟩).symm)

def cpEquiv (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (E : K' ≃ K) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hφ : ∀ k, φ' k = φ (E k)) (hε : ∀ k, ε' k = ε (E k)) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) (𝟙 Y) :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart L φ (fun k => j (E.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have h := Set.mem_iInter.1 hy (E.symm k)
      rw [hφ, E.apply_symm_apply] at h
      exact h
  { idx := fun j k => j (E.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Fintype.prod_equiv E _ _ fun k => ?_
      rw [E.symm_apply_apply, hφ, hε] }

def cpFlat (L : LB X) {I K : Type} [Fintype I] [Fintype K] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) : ChartPull (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb (LB.LinComb L ψ δ) σ e) (𝟙 Y) :=
  have le : ∀ j : I × K → L.ι, LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) j ≤
      (𝟙 Y) ⁻¹ᵁ LB.wchart (LB.LinComb L ψ δ) σ (fun i k => j (i, k)) :=
    fun _ _ hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { idx := fun j i k => j (i, k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L ψ δ) σ e (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i)
        (gm_linComb L ψ δ (𝟙 Y ≫ σ i) y (fun k => j (i, k)) (fun k => j' (i, k))
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_mul, mul_comm (δ k), Category.assoc] }

end Charts

def e4 : Fin 4 ≃ ULift.{0} (Finset (Fin 2)) where
  toFun k := ⟨(![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k⟩
  invFun I := if I.down = {0, 1} then 0 else if I.down = {0} then 1 else if I.down = {1} then 2 else 3
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro I; revert I; decide

theorem finFourEquivSubsetsFinTwo_down_eq (k : Fin 4) : (e4 k).down = (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k := rfl

theorem mumfordSign_finFourEquivSubsetsFinTwo (k : Fin 4) : Oε k = (-1) ^ (2 - (e4 k).down.card) := by
  fin_cases k <;> decide

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem lift_psum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (I : Finset (Fin 2)) :
    (lift u v).left ≫ (psum B (x2 B) I).left = (psum B ![u, v] I).left := by
  rw [← Over.comp_left, comp_psum]
  congr 2
  funext k
  fin_cases k <;> simp [x2]

theorem mumfordBundleFourPoints_eq_lift_comp_partialSum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (k : Fin 4) :
    lamPts u v k = (lift u v).left ≫ (psum B (x2 B) (e4 k).down).left := by
  rw [lift_psum]
  fin_cases k
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_01 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_0 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_1 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_e B u v).symm

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem finFourEquivSubsetsFinTwo_symm_apply (I : ULift.{0} (Finset (Fin 2))) :
    (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) (e4.symm I) = I.down := by
  rw [← finFourEquivSubsetsFinTwo_down_eq, Equiv.apply_symm_apply]

theorem exists_iso_tens : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (L₀ : LB B₀.left) (M : LB B.left), L₀.IsLB → M.IsLB → ∀ (β₂ : (G2 B₀).left ⟶ (G2 B).left) (wR : LB.Iso (abelian₂ B₀ L₀) ((abelian₂ B M).pull β₂)), wR.IsGen → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (Y : Over S₀) (x : Fin r → (Y ⟶ B₀)) (φ : (Fin r × Fin r) × Fin 4 → (Y.left ⟶ B.left)) (ε : (Fin r × Fin r) × Fin 4 → ℤ), (∀ k, φ k = (lift (x k.1.1) (x k.1.2)).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k.2)).left) → (∀ k, ε k = W k.1.1 k.1.2 * Oε k.2) → ∃ v : LB.Iso (LB.LinComb L₀ (tensφ x) (tensε W)) ((LB.LinComb M φ ε).pull (𝟙 Y.left)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y.left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₀ : (Z ⟶ B₀.left) → L₀.ι), Good M z J → Good L₀ z J₀ → GlobalTheory.Mum.Two.isoVal v q z J J₀ = ∏ a, ∏ b, lamVal wR (q ≫ (lift (x a) (x b)).left) z J J₀ ^ W a b := by
  intro S₀ S B₀ _ _ B _ _ L₀ M hL₀ hM β₂ wR hw r W Y x φ ε hφ hε
  let σ : Fin r × Fin r → (Y.left ⟶ (G2 B₀).left) := fun ab => (lift (x ab.1) (x ab.2)).left
  let e : Fin r × Fin r → ℤ := fun ab => W ab.1 ab.2
  let v₁ := transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) wR σ e
  have hv₁ : v₁.IsGen := isGen_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) hw σ e
  let cA : ChartPull (LB.LinComb L₀ (tensφ x) (tensε W)) (LB.LinComb (abelian₂ B₀ L₀) σ e) (𝟙 Y.left) :=
    cpTrans (cpEquiv L₀ (Equiv.prodCongr (Equiv.refl _) e4)
      (fun p : (Fin r × Fin r) × ULift.{0} (Finset (Fin 2)) => σ p.1 ≫ (psum B₀ (x2 B₀) p.2.down).left)
      (fun p => e p.1 * (-1) ^ (2 - p.2.down.card)) _ _
      (fun k => mumfordBundleFourPoints_eq_lift_comp_partialSum (x k.1.1) (x k.1.2) k.2)
      (fun k => by
        show W k.1.1 k.1.2 * Oε k.2 = W k.1.1 k.1.2 * (-1) ^ (2 - (e4 k.2).down.card)
        rw [mumfordSign_finFourEquivSubsetsFinTwo]))
      (cpFlat L₀ (fun I : ULift.{0} (Finset (Fin 2)) => (psum B₀ (x2 B₀) I.down).left)
        (fun I => (-1) ^ (2 - I.down.card)) σ e)
  let cB : ChartPull ((LB.LinComb M φ ε).pull (𝟙 Y.left))
      (LB.LinComb (abelian₂ B M) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)) (𝟙 Y.left) :=
    cpTrans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (LB.LinComb M φ ε) (𝟙 Y.left) (𝟙 Y.left) rfl)
      (cpTrans (cpEquiv M (Equiv.prodCongr (Equiv.prodPUnit _).symm e4)
        (fun q : ((Fin r × Fin r) × PUnit) × ULift.{0} (Finset (Fin 2)) =>
          (σ q.1.1 ≫ β₂) ≫ (psum B (x2 B) q.2.down).left)
        (fun q => (e q.1.1 * 1) * (-1) ^ (2 - q.2.down.card)) φ ε
        (fun k => by rw [hφ k]; exact (Category.assoc _ _ _).symm)
        (fun k => by
          show ε k = (W k.1.1 k.1.2 * 1) * (-1) ^ (2 - (e4 k.2).down.card)
          rw [hε k, mumfordSign_finFourEquivSubsetsFinTwo, _root_.mul_one]))
        (cpFlat M (fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left)
          (fun I => (-1) ^ (2 - I.down.card)) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)))
  let c := cpDiv cA cB
  refine ⟨cGen c v₁, cGen_isGen c hv₁, fun Z q z J J₀ hJ hJ₀ => ?_⟩
  have hm : q z ∈ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y.left)) (LB.LinComb L₀ (tensφ x) (tensε W))).U
      (fun _ k => J (q ≫ 𝟙 Y.left ≫ φ k), fun k => J₀ (q ≫ tensφ x k)) :=
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (q ≫ 𝟙 Y.left ≫ φ k),
      Set.mem_iInter.2 fun k => hJ₀ (q ≫ tensφ x k)⟩
  refine (gm_res q z _ hm _).trans ((gm_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1)
    wR σ e q z (c.idx _) (c.le _ hm)).trans ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => congrArg (· ^ W a b) ?_
  unfold GlobalTheory.PolDeg.lamVal
  have key : ∀ P P', P = P' → gm (q ≫ σ (a, b)) z _ (wR.s P) = gm (q ≫ σ (a, b)) z _ (wR.s P') := by
    rintro _ _ rfl; rfl
  refine key _ _ (Prod.ext (funext fun _ => funext fun I => ?_) (funext fun I => ?_))
  · show J _ = J _
    congr 1
    show q ≫ 𝟙 Y.left ≫ φ ((a, b), e4.symm I) = _
    rw [hφ]
    simp only [finFourEquivSubsetsFinTwo_symm_apply, Category.assoc, Category.id_comp]
  · show J₀ _ = J₀ _
    congr 1
    show q ≫ lamPts (x a) (x b) (e4.symm I) = _
    rw [mumfordBundleFourPoints_eq_lift_comp_partialSum, e4.apply_symm_apply, Category.assoc]

end GlobalTheory.Mum.LamBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantLevelSquareNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThNe

variable {S : Scheme.{0}}

theorem ptSecT_translT_mulT {A : Over S} [GrpObj A] (T : Over S) (y : T ⟶ A) (m : ℕ) :
    ptSecT A (1 : T ⟶ A) ≫ translT A y ≫ mulT A T m = ptSecT A (y ^ m) := by
  have e : ptSecT A (1 : T ⟶ A) ≫ translT A y = ptSecT A y := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [ptSecT, translT]
    · simp only [ptSecT, translT, translPt, Category.assoc, lift_snd, Hom.mul_def, comp_lift_assoc, lift_fst_assoc,
        Category.id_comp]
      rw [← Hom.mul_def, _root_.mul_one]
  rw [← Category.assoc, e]
  apply CartesianMonoidalCategory.hom_ext
  · simp [ptSecT, mulT]
  · simp only [ptSecT, mulT, lift_snd, Category.assoc]
    rw [MonObj.comp_pow, lift_snd]

theorem ne_zero_of_thG {K : Type} [Field K] {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec A))} {m : ℕ} {t : Sp K ⟶ S} {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) (Over.mk t))}
    {y : Over.mk t ⟶ A} {c : K} (H : ThG A L ρ m th y (fn c))
    (hu : ∀ z J, Good L z J → IsUnit (VVRank.sv A th (ptSecT A (y ^ m)).left z J)) : c ≠ 0 := by
  intro hc
  obtain ⟨-, t', α, s₁, θ, -, -, hs₁, hθ, ht, hc'⟩ := H
  obtain ⟨z⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  have q := hc' z J hJ
  have a1 := VVRank.sv_of_isTwistPull A ht (ptSecT A 1).left z hJ
  have a2 := VVRank.sv_of_isTwistPull A hs₁ ((ptSecT A 1).left ≫ (translT A θ.pt).left) z hJ
  have e : ((ptSecT A (1 : Over.mk t ⟶ A)).left ≫ (translT A θ.pt).left) ≫ (mulT A (Over.mk t) m).left =
      (ptSecT A (y ^ m)).left := by
    rw [hθ.pt_eq, ← Over.comp_left, ← Over.comp_left, Category.assoc, ptSecT_translT_mulT]
  rw [e] at a2
  rw [a2] at a1
  have f0 : (fn (0 : K) : Γ((Over.mk t).left, ⊤)) = 0 := map_zero _
  rw [hc, f0, gs_eq _ z ⊤ trivial, map_zero, map_zero, zero_mul] at q
  have q2 := a1.symm.trans q
  rw [Units.mul_right_eq_zero, Units.mul_right_eq_zero] at q2
  exact (hu z J hJ).ne_zero q2

theorem exists_pow_eq_of_card {G : Type} [CommGroup G] {m g : ℕ} (hm : 0 < m)
    (h1 : Nat.card {x : G // x ^ m = 1} = m ^ (2 * g)) (h2 : Nat.card {x : G // x ^ (m ^ 2) = 1} = (m ^ 2) ^ (2 * g))
    (x : G) (hx : x ^ m = 1) : ∃ y : G, y ^ (m ^ 2) = 1 ∧ y ^ m = x := by
  let H2 := (powMonoidHom (m ^ 2) : G →* G).ker
  let H1 := (powMonoidHom m : G →* G).ker
  let f : H2 →* G := (powMonoidHom m).comp H2.subtype
  have cH2 : Nat.card H2 = (m ^ 2) ^ (2 * g) := h2 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H2])
  have cH1 : Nat.card H1 = m ^ (2 * g) := h1 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H1])
  have cK : Nat.card f.ker = m ^ (2 * g) := by
    rw [← h1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, MonoidHom.mem_ker.1 y.2⟩
        invFun := fun x => ⟨⟨x.1, by simp [H2, pow_two, pow_mul, x.2]⟩, MonoidHom.mem_ker.2 x.2⟩
        left_inv := fun y => rfl
        right_inv := fun x => rfl }
  have hpos : 0 < m ^ (2 * g) := pow_pos hm _
  haveI : Finite H2 := Nat.finite_of_card_ne_zero (by rw [cH2]; positivity)
  haveI : Finite H1 := Nat.finite_of_card_ne_zero (by rw [cH1]; positivity)
  have cR : Nat.card f.range = m ^ (2 * g) := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, cK, cH2, show (m ^ 2) ^ (2 * g) = m ^ (2 * g) * m ^ (2 * g) by ring] at e
    exact Nat.eq_of_mul_eq_mul_left hpos e
  have hle : f.range ≤ H1 := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H2, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [H1, f, ← pow_mul, ← pow_two, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [cH1, cR])
  have hx1 : x ∈ H1 := by simpa [H1] using hx
  rw [← heq] at hx1
  obtain ⟨y, hy⟩ := hx1
  exact ⟨y.1, MonoidHom.mem_ker.1 y.2, hy⟩

end GlobalTheory.UMin.ThNe

namespace GlobalTheory.UMin.ThNe

theorem spMap_id_self (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem th_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S)
    (c : Fin N → K), Odd m → 3 ≤ m → (m : K) ≠ 0 → PolFib G L g x → HasTh G L ρ m x c → ∃ a, c a ≠ 0 := by
  intro S G _ _ L ρ hL hρ g m N K _ x c hm hm3 hmK hpol H
  obtain ⟨hLaws, hLaws2⟩ := abelianSchemeLaws_all
  obtain ⟨P, α, -, hα, hPL⟩ := hpol
  haveI := P.isAb.comm
  obtain ⟨ρ', hρ'⟩ := P.rigid
  have H' : HasTh P.A P.L ρ' m (𝟙 (Sp K)) c := by
    rw [hasTh_iff] at H ⊢
    exact (ThMove.hasTh₂_move S G L ρ hL hρ (Sp K) P.A P.L ρ' x α P.isLB hρ' hα hPL m m N N K (𝟙 _) c c).2
      (by rwa [Category.id_comp])
  obtain ⟨θ, pt, hgθ, hl⟩ := H'
  let i : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨pt', -, hl'⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension (Sp K) P.A P.L ρ' P.isLB hρ' m N K (AlgebraicClosure K) i (𝟙 _) θ pt c hl
  have hg' : IsGenSec P.A P.L _ (SecAt.pull P.A P.L θ i) :=
    (gen_of_polFib (Sp K) P.A P.L P.isLB P.g K (𝟙 _) (Model.polFib_self P)).2 θ hgθ (AlgebraicClosure K) i
  have hne := ThetaCoset.ne_zero_of_isGenSec hLaws2.secBaseChangeAny P (spMap i ≫ 𝟙 (Sp K)) hg'
  have hmKb : (m : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hmK
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hLaws.goodPt hLaws.polBaseChange P (spMap i ≫ 𝟙 (Sp K))
    (n := m) (by omega) hmKb _ hne 1
  have c1 := (hLaws.mulN (Sp K) P m (by omega)).2.2.2.2 (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) hmKb
  have c2 := (hLaws.mulN (Sp K) P (m ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by omega)))).2.2.2.2
    (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) (by push_cast; exact pow_ne_zero _ hmKb)
  obtain ⟨y, hy2, hym⟩ := exists_pow_eq_of_card (by omega) c1 c2 (1 * z) (by rw [_root_.one_mul, hz])
  let π : Over.mk (spMap (RingHom.id (AlgebraicClosure K)) ≫ spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp K)) :=
    Over.homMk (spMap (RingHom.id (AlgebraicClosure K))) rfl
  obtain ⟨a, ha⟩ := hl'.2.2 (AlgebraicClosure K) (RingHom.id _) (π ≫ y)
    (by rw [← MonObj.comp_pow, hy2, MonObj.comp_one])
  have hya : y = pt' a := by
    apply Over.OverMorphism.ext
    have := ha
    simp only [π, Over.comp_left, Over.homMk_left] at this
    rwa [spMap_id_self, Category.id_comp, Category.id_comp] at this
  refine ⟨a, fun h0 => ?_⟩
  have hth := hl'.2.1 a
  rw [← hya] at hth
  refine ne_zero_of_thG P.isLB hth (fun p J hJ => ?_) (by show i (c a) = 0; rw [h0, map_zero])
  rw [hym]
  exact hu p J hJ

end GlobalTheory.UMin.ThNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_thList : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  intro S G _ _ L ρ hL hρ g m N K _ _ x θ hm hmK hN hP
  subst hN
  obtain ⟨pt, hinj, hpt, hall⟩ := GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre S G L g m K x hmK hP
  choose c hc using fun a => GlobalTheory.T.exists_thetaConstant_m_sq_torsion_algClosed_fibre S G L ρ hL hρ g m K x θ (pt a) hm hmK hP (hpt a)
  exact ⟨pt, c, hinj, hc, hall⟩

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_theta_local {S : Scheme.{0}} (G : Over S) [GrpObj G] (hA : IsAbelianScheme G)
    (L : LB G.left) (hL : L.IsLB) (U : Type) [CommRing U] [IsLocalRing U] (u : Sp U ⟶ S) (n : ℕ)
    (x : Over.mk u ⟶ G) (hx : x ^ n = 1) : ∃ θ : ThetaGrp G L (n : ℤ) (Over.mk u), θ.pt = x := by
  have := hA.comm
  set a : Over.mk u ⊗ G ⟶ G := fst (Over.mk u) G ≫ x with ha
  set y : Over.mk u ⊗ G ⟶ G := snd (Over.mk u) G with hy
  have cube := GlobalTheory.CubeTop.cubeTheorem S G hA L hL (Over.mk u ⊗ G)
  have key : ∀ m : ℕ, ∃ t : LB.Gen (LB.LinComb L
      ![(a ^ m * y).left, (a ^ m).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left]
      ![1, -1, -(m : ℤ), (m : ℤ), (m : ℤ) - 1, 1 - (m : ℤ)]), t.IsGen := by
    intro m
    induction m with
    | zero =>
      obtain ⟨t, ht⟩ := cube 1 a y
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ 0 * y).left, (a ^ 0).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ) - 1, 1 - ((0 : ℕ) : ℤ)]) (fun V _ g => by
          simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
            Matrix.cons_val_one, pow_zero, _root_.one_mul]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module) t ht
      exact ⟨t', ht'⟩
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨c, hc⟩ := cube (a ^ m) a y
      have e₁ : a ^ m * a * y = a ^ (m + 1) * y := by rw [pow_succ]
      have e₂ : a ^ m * a = a ^ (m + 1) := by rw [pow_succ]
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ (m + 1) * y).left, (a ^ (m + 1)).left, (a * y).left, a.left, y.left,
          (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ) - 1, 1 - ((m + 1 : ℕ) : ℤ)])
        (fun V _ g => by
          rw [Fintype.prod_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Matrix.cons_val_one, e₁, e₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module)
        (LB.mulGen L _ _ _ _ t c) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hc)
      exact ⟨t', ht'⟩
  obtain ⟨t, ht⟩ := key n
  have han : a ^ n = 1 := by rw [ha, ← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := U) L hL (K := Fin 2)
    ![x.left, (1 : Over.mk u ⟶ G).left] ![-(n : ℤ), n]
  have h1 : (fst (Over.mk u) G).left ≫ (1 : Over.mk u ⟶ G).left = (1 : Over.mk u ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk u) G).left ≫ x.left = a.left := rfl
  have h3 : translPt G x = a * y := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (Over.mk u) G).left, (translPt G x).left]) (ε' := ![(n : ℤ), -(n : ℤ)]) (fun V _ g => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, han, h1, h2, h3, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ e (fst (Over.mk u) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.WeilSpecialise

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem unitOn_surjective {R : Type} [CommRing R] : Function.Surjective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective.2

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_specialise : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (Lb : LB G.left), Lb.IsLB → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ (P Q : Over.mk u ⟶ G) (c : Uˣ), P ^ n = 1 → Q ^ n = 1 → ∀ (P' Q' : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), P'.left = spMap (algebraMap U Ω) ≫ P.left → Q'.left = spMap (algebraMap U Ω) ≫ Q.left → Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → ∀ (k : Type) [Field k] (h : U →+* k) (P₀ Q₀ : Over.mk (spMap h ≫ u) ⟶ G), P₀.left = spMap h ≫ P.left → Q₀.left = spMap h ≫ Q.left → Out.WeilIs G Lb n P₀ Q₀ (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω _ _ _ _ _ _ S G _ hA Lb hLb u n _ P Q c hP hQ P' Q' hP' hQ' HΩ k _ h P₀ Q₀ hP₀ hQ₀
  have hG := globalFns_holds
  have loc : ∀ z : Over.mk u ⟶ G, z ^ n = 1 → ∀ p : (Over.mk u).left, ∃ V : (Over.mk u).left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp G Lb (n : ℤ) (overRes V), θ.pt = overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_local G hA Lb hLb U u n z hz
    obtain ⟨θ', h'⟩ := GlobalTheory.CommutatorPairing.exists_pull hLb θ (overResι (⊤ : (Over.mk u).left.Opens))
    exact ⟨⊤, trivial, θ', h'.trans (by rw [hθ])⟩
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hLb (loc P hP) (loc Q hQ)
  obtain ⟨c₁, rfl⟩ := unitOn_surjective c₀
  let iΩ : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ Over.mk u := Over.homMk (spMap (algebraMap U Ω)) rfl
  have eP : P' = iΩ ≫ P := Over.OverMorphism.ext hP'
  have eQ : Q' = iΩ ≫ Q := Over.OverMorphism.ext hQ'
  have H₁ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb iΩ hc₀
  rw [← eP, ← eQ] at H₁
  have H₁' : Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω).toMonoidHom c₁)) := by
    rw [← map_unitOn]; exact H₁
  have e := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLb H₁' HΩ
  have e' := unitOn_inj e
  have hc : c₁ = c := Units.ext (IsFractionRing.injective U Ω (congrArg Units.val e'))
  subst hc
  let ik : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  have eP₀ : P₀ = ik ≫ P := Over.OverMorphism.ext hP₀
  have eQ₀ : Q₀ = ik ≫ Q := Over.OverMorphism.ext hQ₀
  have H₂ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb ik hc₀
  rw [← eP₀, ← eQ₀] at H₂
  have := map_unitOn h c₁
  exact this ▸ H₂

end GlobalTheory.WeilSpecialise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsFiniteExtensionGaloisEquivari
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_labels_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (n : ℕ), OneTrait D.toPre A lab → GalEqN n lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → 1 ≤ n → ∃ lab₁ : Labels D₁.toPre A₁, OneTrait D₁.toPre A₁ lab₁ ∧ GalEqN n lab₁ := by
  intro R _ _ _ hB D A lab n hOne hGal R₁ _ _ _ ρ hρ D₁ hD A₁ a hfib hn
  obtain ⟨hD⟩ := hD
  obtain ⟨_, em, lab₁, hc, hOne₁, hrel⟩ :=
    exists_labels_finExt_emb R hB D A lab hOne R₁ ρ hρ D₁ hD A₁ a hfib
  exact ⟨lab₁, hOne₁, LabBC.galEqN_of_rel ρ hρ D D₁ hD A A₁ a hfib lab n hn hGal em lab₁ hc hrel⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBaseStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base : GlobalTheory.Published.CubeTheorem := by
  first | exact @GlobalTheory.CubeTop.cubeTheorem | exact GlobalTheory.CubeTop.cubeTheorem | (intros; apply GlobalTheory.CubeTop.cubeTheorem <;> assumption)
end

