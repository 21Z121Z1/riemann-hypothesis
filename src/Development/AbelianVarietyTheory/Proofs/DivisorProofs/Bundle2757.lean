import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumLeftPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.AdjComp

section Iso

variable {X : Scheme.{0}}

theorem gm_iso {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z)
    (i j : B.ι × A.ι) (hi : f z ∈ B.U i.1 ⊓ A.U i.2) (hj : f z ∈ B.U j.1 ⊓ A.U j.2) :
    gm f z (B.U i.1 ⊓ A.U i.2) (w.s i) =
      gm f z (B.U i.1 ⊓ B.U j.1) (B.g i.1 j.1) * (gm f z (A.U i.2 ⊓ A.U j.2) (A.g i.2 j.2))⁻¹ *
        gm f z (B.U j.1 ⊓ A.U j.2) (w.s j) := by
  have hm : f z ∈ B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2) := ⟨hi, hj⟩
  have e := congrArg (gm f z (B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2))) (hw i j)
  exact (gm_res f z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B f z i j hm) (gm_res f z _ hm _))))

variable {A B C : LB X}

theorem exists_comp (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (w₁ : LB.Iso A B) (hw₁ : w₁.IsGen)
    (w₂ : LB.Iso B C) (hw₂ : w₂.IsGen) :
    ∃ w : LB.Iso A C, w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (r : C.ι) (p : B.ι) (q : A.ι),
      f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z (C.U r ⊓ A.U q) (w.s (r, q)) =
        gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
  have glue : ∀ (r : C.ι) (q : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U q)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z)
      (p : B.ι), f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z _ s = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
    intro r q
    let W : B.ι → X.Opens := fun p => C.U r ⊓ A.U q ⊓ B.U p
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U q := fun p => inf_le_left
    have l₂ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ B.U p ⊓ A.U q := fun p x hx => ⟨hx.2, hx.1.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₂ p) (w₂.s (r, p)) * res (l₁ p) (w₁.s (p, q))
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : B.ι) (hz : f z ∈ W p),
        gm f z (W p) (u p) = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) :=
      fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₂ p) hz _) (gm_res f z (l₁ p) hz _))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩) u (fun p p' x hx => by
        rw [hu _ (𝟙 X) x p hx.1, hu _ (𝟙 X) x p' hx.2]
        have a₂ := gm_iso hw₂ (𝟙 X) x (r, p) (r, p') ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩
        have a₁ := gm_iso hw₁ (𝟙 X) x (p, q) (p', q) ⟨hx.1.2, hx.1.1.2⟩ ⟨hx.2.2, hx.2.1.2⟩
        rw [a₂, a₁, gm_self hC (𝟙 X) x hx.1.1.1, gm_self hA (𝟙 X) x hx.1.1.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z f z p hr hp hq => ?_⟩
    have hy : f z ∈ W p := ⟨⟨hr, hq⟩, hp⟩
    exact (gm_res f z (l₀ p) hy s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hu Z f z p hy))
  choose s hs using glue
  refine ⟨⟨fun rq => s rq.1 rq.2⟩, fun i j => unit_ext fun x hx => ?_, fun Z f z r p q hr hp hq => hs r q Z f z p hr hp hq⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have e₁ := hs i.1 i.2 _ (𝟙 X) x p hx.1.1 hp hx.1.2
  have e₂ := hs j.1 j.2 _ (𝟙 X) x p hx.2.1 hp hx.2.2
  have a₂ := gm_iso hw₂ (𝟙 X) x (i.1, p) (j.1, p) ⟨hx.1.1, hp⟩ ⟨hx.2.1, hp⟩
  have a₁ := gm_iso hw₁ (𝟙 X) x (p, i.2) (p, j.2) ⟨hp, hx.1.2⟩ ⟨hp, hx.2.2⟩
  refine (gm_res (𝟙 X) x _ hx _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A C (𝟙 X) x i j hx) ((gm_res (𝟙 X) x _ hx _).trans e₂)).trans ?_
  rw [a₂, a₁, gm_self hB (𝟙 X) x hp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

end Iso

section Pull

variable {Y Y' : Scheme.{0}} {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y}

theorem pullIso_le (a : ChartPull A' A h) (b : ChartPull B' B h) (p : B'.ι × A'.ι) :
    B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
  fun _ hy => ⟨b.le _ hy.1, a.le _ hy.2⟩

def pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) : LB.Iso A' B' :=
  ⟨fun p => res (pullIso_le a b p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩

theorem gm_pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) {Z : Scheme.{0}} (r : Z ⟶ Y')
    (z : Z) (p : B'.ι × A'.ι) (hp : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullIso a b w).s p) =
      gm (r ≫ h) z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
  (gm_res r z (pullIso_le a b p) hp _).trans (gm_pull r h z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (pullIso_le a b p hp) _)

theorem pullIso_isGen (a : ChartPull A' A h) (b : ChartPull B' B h) {w : LB.Iso A B} (hw : w.IsGen) :
    (pullIso a b w).IsGen := fun p q => unit_ext fun y hy => by
  have hp : (𝟙 Y' ≫ h) y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) := ⟨b.le _ hy.1.1, a.le _ hy.1.2⟩
  have hq : (𝟙 Y' ≫ h) y ∈ B.U (b.idx q.1) ⊓ A.U (a.idx q.2) := ⟨b.le _ hy.2.1, a.le _ hy.2.2⟩
  have l := gm_iso hw (𝟙 Y' ≫ h) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hp hq
  have e₁ := (gm_res (𝟙 Y') y inf_le_left hy _).trans (gm_pullIso a b w (𝟙 Y') y p hy.1)
  have e₂ := (gm_res (𝟙 Y') y inf_le_right hy _).trans (gm_pullIso a b w (𝟙 Y') y q hy.2)
  refine e₁.trans (l.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A' B' (𝟙 Y') y p q hy) e₂).trans ?_
  rw [b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, Category.id_comp]

end Pull

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam.AdjComp

theorem psum_left_pull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) (I : ULift (Finset (Fin n))) :
    (psum G x' I.down).left = m.left ≫ (psum G x I.down).left := by
  obtain rfl : x' = fun i => m ≫ x i := funext hx
  rw [← Over.comp_left, comp_psum]

def cubePull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (L : LB G.left) (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) :
    ChartPull (cubeLB G x' L) (cubeLB G x L) m.left :=
  chartPullSame L _ _ _ m.left (psum_left_pull m x x' hx)

theorem adjVal_of {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) (j₁ : ULift (Finset (Fin 2)) → L₁.ι)
    (j₂ : ULift (Finset (Fin 2)) → L₂.ι) (h₁ : ∀ I, J₁ (p ≫ (psum G₁ x₁ I.down).left) = j₁ I)
    (h₂ : ∀ I, J₂ (p ≫ (psum G₂ x₂ I.down).left) = j₂ I) :
    adjVal w p z J₁ J₂ = gm p z ((cubeLB G₁ x₁ L₁).U j₁ ⊓ (cubeLB G₂ x₂ L₂).U j₂) (w.s (j₁, j₂)) := by
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₁ (p ≫ (psum G₁ x₁ I.down).left)) = j₁ := funext h₁
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₂ (p ≫ (psum G₂ x₂ I.down).left)) = j₂ := funext h₂
  rfl

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam

open AdjComp in

theorem Adj.comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ Q₃ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) (b : Q₂.B ⟶ Q₃.B) (b' : Q₃.B ⟶ Q₂.B) (k : Q₂.X →+ Q₃.X)
    (k' : Q₃.X →+ Q₂.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₃ b b' k k' →
      Adj Q₁ Q₃ (a ≫ b) (b' ≫ a') (k.comp h) (h'.comp k') := by
  intro R _ _ Q₁ Q₂ Q₃ a a' h h' b b' k k' H₁ H₂
  obtain ⟨ma, ma', ca, ca', w₁₂, g₁₂, V₁₂⟩ := H₁
  obtain ⟨mb, mb', cb, cb', w₂₃, g₂₃, V₂₃⟩ := H₂
  let m₁ : Q₁.B ⊗ Q₃.B ⟶ Q₂.B ⊗ Q₃.B := lift (fst _ _ ≫ a) (snd _ _)
  let m₂ : Q₁.B ⊗ Q₃.B ⟶ Q₁.B ⊗ Q₂.B := lift (fst _ _) (snd _ _ ≫ b')
  have xA : ∀ i, (![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B ≫ b, snd Q₂.B Q₃.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₁ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B, snd Q₂.B Q₃.B ≫ b'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₂ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cA := cubePull Q₃.M.L m₁ _ _ xA
  let cB₁ := cubePull Q₂.M.L m₁ _ _ xB₁
  let cB₂ := cubePull Q₂.M.L m₂ _ _ xB₂
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] Q₃.M.L).IsLB := DVR.linComb_isLB _ Q₃.M.isLB _ _
  have lB : (cubeLB Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC (pullIso cA cB₁ w₂₃) (pullIso_isGen cA cB₁ g₂₃)
    (pullIso cB₂ cC w₁₂) (pullIso_isGen cB₂ cC g₁₂)
  refine ⟨inferInstance, inferInstance, fun y => ?_, fun y => ?_, w, gw, fun y y' z J₁ J₃ hJ₁ hJ₃ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb, ca, Category.assoc]
  · rw [AddMonoidHom.comp_apply, ca', cb', Category.assoc]
  · obtain ⟨J₂, hJ₂⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' Q₂.M.isLB z
    have e₂₃ := V₂₃ (h y) y' z J₂ J₃ hJ₂ hJ₃
    have e₁₂ := V₁₂ y (k' y') z J₁ J₂ hJ₁ hJ₂
    have hP₂₃ : (lift (toUnit (TK R) ≫ Q₂.c (h y)) (toUnit (TK R) ≫ Q₃.c y')).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₁.left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, ca, Category.assoc]
    have hP₁₂ : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c (k' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, cb', Category.assoc]
    rw [hP₂₃] at e₂₃
    rw [hP₁₂] at e₁₂
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left = P at e₂₃ e₁₂ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] I.down).left) P
    have mB := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] I.down).left) P
    have mA := Good.mem hJ₃ (fun I : ULift (Finset (Fin 2)) => (psum Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] I.down).left) P
    have K : adjVal w P z J₁ J₃ = adjVal w₂₃ (P ≫ m₁.left) z J₂ J₃ * adjVal w₁₂ (P ≫ m₂.left) z J₁ J₂ := by
      refine ((adjVal_of w P z J₁ J₃ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB₂ cC w₁₂ P z (_, _) ⟨mC, mB⟩) (gm_pullIso cA cB₁ w₂₃ P z (_, _) ⟨mB, mA⟩)))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂₃ (P ≫ m₁.left) z J₂ J₃ _ _ (fun I => ?_) (fun I => ?_)).symm
        (adjVal_of w₁₂ (P ≫ m₂.left) z J₁ J₂ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xB₁ I]
      · show J₃ _ = J₃ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xA I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB₂ I]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e₂₃, e₁₂, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtR
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev ptR (χ : D.X) : Spec (CommRingCat.of R) ⟶ D.P.A.left :=
  (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ D.c χ).left

def unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) :
    (FractionRing R)ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
    (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).toMonoidHom

def Reads (κ : D.X → (FractionRing R)ˣ) : Prop :=
  ∃ g : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptR D χ) (fun _ => -1)),
    (∀ χ, (g χ).IsGen) ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi χ) r z J = unitAt r z (κ χ) * val (g χ) (r ≫ jK R) z J

def lead {X : Type} [AddCommGroup X] (κ : X → (FractionRing R)ˣ) (k : ℕ) (α mu : X) : (FractionRing R)ˣ :=
  κ mu ^ k * (κ (mu + α) * (κ mu)⁻¹ * (κ α)⁻¹)

end GlobalTheory.ThFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (inc : G ⟶ G'), IsMonHom inc → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → ∃ t : LB.Gen (letI := A'.isAb.comm; (abelian₂ A'.A A'.L).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.f) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left), t.IsGen := by
  first | exact @GlobalTheory.Mum.pull_gen_lam_generic | exact GlobalTheory.Mum.pull_gen_lam_generic | (intros; apply GlobalTheory.Mum.pull_gen_lam_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFrameEndomorphismMatrix
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory

namespace GlobalTheory.SectionPull

theorem canonical_app_pullbackSections {X T : Scheme.{0}} (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X)
    (F : X.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫
        (Scheme.Modules.pullbackId _).hom.app F).app ⊤
      (QCoh.pullbackSections t _ (le_refl (⊤ : X.Opens))
        (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) s)) = s := by
  have H {j j' : X ⟶ X} (w : j = j') (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ ⊤) (hj' : (⊤ : X.Opens) ≤ j' ⁻¹ᵁ ⊤) :
      ((Scheme.Modules.pullbackCongr w).hom.app F).app ⊤ (QCoh.pullbackSections j F hj s) =
        QCoh.pullbackSections j' F hj' s := by
    subst w; rfl
  have e1 := PullPull.pullbackComp_hom_app t c F (U := ⊤) (V := ⊤) (T := ⊤) (le_refl _) (le_refl _)
    (le_refl (⊤ : X.Opens)) s
  have e2 := H h (le_refl (⊤ : X.Opens)) (le_refl (⊤ : X.Opens))
  have e3 := PullPull.pullbackId_hom_app F (U := ⊤) (V := ⊤) (le_refl _) (le_refl _) s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [e1, e2, e3, Twist.resM_self]

theorem pullback_map_comp_canonical : ∀ (X T : Scheme.{0}) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) (F : X.Modules) (κ : Type) [Fintype κ] (e : κ → Γ(F, ⊤)), VB.IsFrame e → ∀ (Φ : (Scheme.Modules.pullback c).obj F ⟶ (Scheme.Modules.pullback c).obj F) (B : Matrix κ κ Γ(T, ⊤)), (∀ i, Φ.app ⊤ (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) = ∑ j, B j i • QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j)) → ∀ (ψ : F ⟶ F), (∀ i, ψ.app ⊤ (e i) = ∑ j, t.appTop (B j i) • e j) → (Scheme.Modules.pullback t).map Φ ≫ (Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F = ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F) ≫ ψ := by
  intro X T c t h F κ _ e he Φ B hΦ ψ hψ
  haveI := he.isVB.isQuasicoherent
  have hc := he.pullback c
  have ht : VB.IsFrame fun i => QCoh.pullbackSections t ((Scheme.Modules.pullback c).obj F)
      (le_refl (⊤ : X.Opens)) (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) :=
    hc.pullback t
  refine LieVB.hom_ext_of_isFrame ht fun i => ?_
  rw [Scheme.Modules.Hom.comp_app ((Scheme.Modules.pullback t).map Φ), Scheme.Modules.Hom.comp_app _ ψ,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, canonical_app_pullbackSections, hψ]
  have e1 := QCoh.pullback_map_app_pullbackSections t Φ (U := ⊤) (V := ⊤) (le_refl _)
    (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i))
  erw [e1]
  rw [hΦ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 := QCoh.pullbackSections_smul t ((Scheme.Modules.pullback c).obj F) (U := ⊤) (V := ⊤)
    (le_refl _) (B j i) (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j))
  erw [e2, Scheme.Modules.Hom.app_smul, canonical_app_pullbackSections]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.SectionPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFreeModuleIso
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

theorem GlobalTheory.pullback_freeModule_iso_free : ∀ (S T : Scheme.{0}) (f : S ⟶ T) (n : ℕ), Nonempty ((Scheme.Modules.pullback f).obj (GlobalTheory.QCoh.freeModule (X := T) (Fin n)) ≅ GlobalTheory.QCoh.freeModule (X := S) (Fin n)) := by
  intro S T f n
  exact ⟨((VB.isFrame_freeFrame T (Fin n)).pullback f).iso (VB.isFrame_freeFrame S (Fin n))⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackCoordinateCombinationRatioAndVanishStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBack_coordinate_combination_ratio_and_vanish : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    (∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
          ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i)) ∧
    (y ≠ 0 → ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, algebraMap K Ω (lam k : K) * y k = 0 →
        ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) := by
  first | exact @GlobalTheory.PullCoordComb.linComb_ratio_and_vanish | exact GlobalTheory.PullCoordComb.linComb_ratio_and_vanish | (intros; apply GlobalTheory.PullCoordComb.linComb_ratio_and_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

namespace GlobalTheory.PDForm

theorem quot_fil_rel : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  intro R B _ _ _ J δ G _ _ J' δ' q h n hd hq hJ hk
  obtain ⟨-, -, hsurj, hker⟩ := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R B G q h hq
  obtain ⟨-, -, hmul, -, -, hanti, -⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  have hv : ∀ m, ∀ a ∈ J, (0 : Derivation R B B) (δ.dpow (m + 1) a) = δ.dpow m a * (0 : Derivation R B B) a := by
    intro m a _; simp
  have hd0 := ((GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2 R B J δ 0 hv n).2.1
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  ·
    have hle : rel R δ' ≤ (rel R δ).map h.mDR := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨m, a', ha', rfl⟩
      rw [hJ, Ideal.mem_map_iff_of_surjective _ hq] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      have e : ι1 (D R G (δ'.dpow (m + 1) (q a)) - δ'.dpow m (q a) • D R G (q a)) =
          h.mDR (ι1 (D R B (δ.dpow (m + 1) a) - δ.dpow m a • D R B a)) := by
        rw [h.mDR_ι, map_sub h.m1, h.m1_D, h.oneFormMap_smul_semilinear, h.m1_D, hd.2 a ha, hd.2 a ha]
      rw [e]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, a, ha, rfl⟩)
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 (hle hx)
    have hK : x - y ∈ filDR R δ n := by
      refine hker (filDR R δ n) (hmul n) (fun b hb ↦ ?_) (x - y) (by rw [map_sub, hxy, sub_self])
      have hb1 : algebraMap B (DR R B) b ∈ filDR R δ (n + 1) :=
        Ideal.mem_sup_left (Ideal.subset_span ⟨b, (hk b).1 hb, rfl⟩)
      refine ⟨hanti n (n + 1) (Nat.le_succ n) hb1, ?_⟩
      rw [← dDR_algebraMap]
      exact hd0 _ hb1
    have hyn : y ∈ filDR R δ n := Ideal.mem_sup_right hy
    simpa using add_mem hK hyn
  · have hle : filDR R δ (n + 1) ≤ (rel R δ').comap h.mDR := by
      refine sup_le (Ideal.span_le.2 ?_) (fun z hz ↦ mDR_mem_rel h hd hz)
      rintro _ ⟨b, hb, rfl⟩
      change h.mDR (algebraMap B _ b) ∈ rel R δ'
      rw [h.mDR_algebraMap, (hk b).2 hb, map_zero]
      exact zero_mem _
    exact hle hx

end GlobalTheory.PDForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugateStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_relativeFrobenius_primitiveDeRham_eq_conjugate : GlobalTheory.Published.AbelianDeRham.BaseChange → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left) (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) (F : A ⟶ A₁) [IsMonHom F] (hF : F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A)) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LinearMap.range (primPull (dp0 R) (𝟙 _) F) = conjDR p R hR A ∧ PrimitiveSubmodule A₁ ≤ LinearMap.ker (primPull (dp0 R) (𝟙 _) F) := by
  first | exact @GlobalTheory.ConjSeq.range_primPull_relFrob | exact GlobalTheory.ConjSeq.range_primPull_relFrob | (intros; apply GlobalTheory.ConjSeq.range_primPull_relFrob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagBundleSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.CovTest.Multisection

theorem nonempty_flag_of_field (K : Type) [Field K] (F : (Spec (CommRingCat.of K)).Modules)
    (hF : VB.IsVB F 2) : Nonempty (Vert.Flag F 2) := by
  have key : ∀ (G : (Spec (CommRingCat.of K)).Modules) (r : ℕ), VB.IsVB G r →
      ∃ e : Fin r → Γ(G, ⊤), VB.IsFrame e := by
    intro G r h
    obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint K)
    have hU : ⊤ ≤ U := fun x _ => (Subsingleton.elim x (IsLocalRing.closedPoint K)) ▸ hx
    exact ⟨_, he.res hU⟩
  have hO := VB.isVB_structureModule (Spec (CommRingCat.of K))
  obtain ⟨e, he⟩ := key F 2 hF
  obtain ⟨e', he'⟩ := key _ 2 (hO.biprod hO)
  exact ⟨(Vert.Flag.ofBiprod hO hO).ofIso (he'.iso he)⟩

theorem exists_multisection : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p) (E : B.Modules),
    GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ Y), IsArithVar (i ≫ p) d ∧
      (i ≫ π) (genericPoint Z) = genericPoint B ∧ (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
  intro k _ B Y _ _ q p d hq hp π w E hE fl hfl
  let K : Type := B.residueField (genericPoint B)
  let g : Spec (CommRingCat.of K) ⟶ B := B.fromSpecResidueField (genericPoint B)
  obtain ⟨fl'⟩ := nonempty_flag_of_field K ((Scheme.Modules.pullback g).obj E) (hE.pullback g)
  obtain ⟨g', ⟨hg', -⟩, -⟩ := hfl _ g (fun _ => fl')
  have hc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g'
  obtain ⟨e₁, d₁⟩ := ProjDrop.deg_eq_of_fieldPoint π (g' (IsLocalRing.closedPoint K)) (genericPoint B)
    (Ω := K) _ (𝟙 (B.residueField (genericPoint B)) : B.residueField (genericPoint B) ⟶ CommRingCat.of K)
    (by rw [hc, hg', Spec.map_id]; exact (Category.id_comp _).symm)
  have h1 : ProjDrop.deg (𝟙 (B.residueField (genericPoint B)) :
      B.residueField (genericPoint B) ⟶ CommRingCat.of K).hom = 1 := by
    rw [CommRingCat.hom_id]
    exact ProjDrop.deg_equiv (RingEquiv.refl K)
  have hn : π.residueDegree (g' (IsLocalRing.closedPoint K)) ≠ 0 := by
    intro h
    rw [h1, h, zero_mul] at d₁
    exact one_ne_zero d₁
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (g' (IsLocalRing.closedPoint K))
  have g₁ : (i ≫ π) (genericPoint Z) = genericPoint B := by rw [Scheme.Hom.comp_apply, hi, e₁]
  have n₁ : (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact hn
  have hproj : IsProjOver (i ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion i hp.isProjOver
  have hflat : Flat ((i ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    haveI := hq.flat
    haveI : CharZero (B.residueField ((i ≫ π) (genericPoint Z))) :=
      g₁.symm ▸ DimCover.charZero_residueField (q ≫ spMap (Int.castRingHom k))
    haveI := (RingHom.charZero_iff ((i ≫ π).residueFieldMap (genericPoint Z)).hom.injective).mp this
    exact ProjDrop.charZero_of_residueField (genericPoint Z)
  refine ⟨Z, inferInstance, i, ⟨hq.isDomain, hq.finite, inferInstance, hproj, hflat,
    DimCover.topologicalKrullDim_eq k B Z q (i ≫ p) d hq hproj hflat (i ≫ π)
      (by rw [Category.assoc, w]) g₁ n₁⟩, g₁, n₁⟩

end GlobalTheory.CovTest.Multisection

end
end

