import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0005
import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PartnersFactorsOfKernelSmith
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SmithPairing
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.JointsLit

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualFlatOf
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def kapTen (p : ℕ) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : ℕ :=
  ∑ x : TT × Bool, m * Nat.log p (hhDeg aT bT x.1.val x.2)

def DualLatAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    ∃ Ψ : Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT),
      (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
        (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O) ≤
                  HHL ι σ TT aT bT (latDual L) ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (HHL (O := O) ι σ TT aT bT (latDual L)) ≤
          (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
        (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O) ≤ ReHH p ι σ w TT aT bT e.dual ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (ReHH p ι σ w TT aT bT e.dual) ≤
          (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O)

def DualFlatAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    (∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → IsEdge p n' 1 e.dual ∧ e.dual.dual = e) ∧
    ∃ Ψ : Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT),
      (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
        (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O) ≤
                  HHL ι σ TT aT bT (latDual L) ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (HHL (O := O) ι σ TT aT bT (latDual L)) ≤
          (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
        (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O) ≤ ReHH p ι σ w TT aT bT e.dual ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (ReHH p ι σ w TT aT bT e.dual) ≤
          (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def topOdd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT :=
  ⟨segPos X.TT j i, (pos_mem X.TT j i).1⟩

def topEnd (X : Loc) (j : Fin (numSeg X.TT)) : X.TT :=
  ⟨segNext X.TT j, (next_mem X.TT j).1⟩

def symVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → (X.TT × Bool) × Fin (X.m + 1)
  | Sum.inl (a, c) =>
    if h : (a : ℕ) < 2 * segS X.TT j then
      ((topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0)), c.succ)
    else ((topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j)), c.succ)
  | Sum.inr (l, b) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then
      ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩), !b), 0)
    else ((topEnd X j, !b), 0)

def symLev (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ
  | Sum.inl (a, _) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (X.seg C0 CE1 CE2 j).P p ⟨(a : ℕ) / 2, by omega⟩ else 1
  | Sum.inr (l, _) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then (X.seg C0 CE1 CE2 j).P p (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩) else 1

def digitMon (K : Type*) [CommSemiring K] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    MvPolynomial.X ((topOdd X j i, true), c) ^ b.rz i c * MvPolynomial.X ((topOdd X j i, false), c) ^ b.ry i c

def sTopMon (K : Type*) [CommSemiring K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    MvPolynomial.X ((topOdd X j i, true), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * (coarseA p (X.seg C0 CE1 CE2 j) b i - b.w i)) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * b.sg i)
  else 1

def ioBlock (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b *
    aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v) u

def symFam (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ j, ioBlock K p C0 CE1 CE2 X j (β j) (s j)

def Lemma44At (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) (β j)).SSZ O (r := X.m)) →
      ∃ F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        InA (C (algebraMap O (KK O) (S.w ^ (∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)))) * F) ∧
        InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c ∧
        ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
          ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g → InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g' F X.c

def BinomialRatioBeyondThreshold : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => Lemma44At C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def IsFlatTheta {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O) (φ : WF p n' ≃+* W) {m : ℕ} (TT : Finset (Fin n'))
    (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT)) : Prop :=
  letI : Algebra (WF p n') O := algOfIdent jO φ
  (∀ F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O),
      InA (O := O) (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) ↔
      Θ F ∈ HHL (O := O) ι σ TT aT bT (colSpan W h)) ∧
    (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
      ∀ e : Edge W Qq (m + 1), IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
        ∀ (F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (i : ℕ),
          InWjRg p n' O w 1 (hhLetters TT) g (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) i ↔
          Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (ReHH p ι σ w TT aT bT e)) ∧
    ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → e.src = colSpan W h →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g ∧ IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose)

def SrcHalfAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∀ φ : WF X.p X.n' ≃+* W, IsWittIdent σ φ →
    ∀ (h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) Qq) Θ, IsFlatTheta ι σ jO w φ X.TT X.aT X.bT h Θ →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e → e.src = colSpan W h →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      IsEdgeBasis X.p 1 e (h * ((matQ φ g)⁻¹).transpose) →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (X.m0 Cm) (β j)).SSZ O (r := X.m)) →
      ∃ F, Θ F ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
        (letI : Algebra (WF X.p X.n') O := algOfIdent jO φ
         InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) g
           (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FockZeroRight
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_coe_basis {E : Type} [AddCommGroup E] [Module O E] (Λ : Submodule O E) {n : ℕ}
    (B : Module.Basis (Fin n) O Λ) : Submodule.span O (Set.range fun i => (B i : E)) = Λ := by
  have h : (Set.range fun i => (B i : E)) = Λ.subtype '' Set.range B := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem fock_zero_right {σ : Type} (F : MvPolynomial σ (KK O)) : fock F (0 : MvPolynomial σ (KK O)) = 0 := by
  simp [fock]

theorem smith_block {σ : Type} (Λ : Submodule O (MvPolynomial σ (KK O))) (hfg : Module.Finite O Λ) :
    ∃ (n : ℕ) (al be : Fin n → MvPolynomial σ (KK O)), (∀ i, al i ∈ Λ ∧ be i ∈ Λ) ∧
      (∀ i l, i ≠ l → fock (al i) (be l) = 0) ∧ LinearIndependent O al ∧
      Submodule.span O (Set.range al) = Λ ∧ Submodule.span O (Set.range be) = Λ := by
  classical
  haveI : Module.Free O Λ := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O Λ
  obtain ⟨P, Q, hP, hQ, hd⟩ := Formalism.InvariantFactorPaths.KP.smithPairing O (KK O) (Module.finrank O Λ)
    (Matrix.of fun a c => fock (e a : MvPolynomial σ (KK O)) (e c : MvPolynomial σ (KK O)))
  have hPt : IsUnit P.transpose.det := by rw [Matrix.det_transpose]; exact hP
  let alB := e.map (Matrix.toLinearEquiv e P.transpose hPt)
  let beB := e.map (Matrix.toLinearEquiv e Q hQ)
  have hal : ∀ i, (alB i : MvPolynomial σ (KK O)) = ∑ a, P i a • (e a : MvPolynomial σ (KK O)) := fun i => by
    show ((Matrix.toLin e e P.transpose (e i) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp [Matrix.transpose_apply]
  have hbe : ∀ l, (beB l : MvPolynomial σ (KK O)) = ∑ c, Q c l • (e c : MvPolynomial σ (KK O)) := fun l => by
    show ((Matrix.toLin e e Q (e l) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp
  refine ⟨_, fun i => (alB i : MvPolynomial σ (KK O)), fun i => (beB i : MvPolynomial σ (KK O)),
    fun i => ⟨(alB i).2, (beB i).2⟩, fun i l hil => ?_, ?_, span_coe_basis Λ alB, span_coe_basis Λ beB⟩
  · have h := hd i l hil
    show fock (alB i : MvPolynomial σ (KK O)) (beB l : MvPolynomial σ (KK O)) = 0
    rw [hal, hbe, fock_bilin]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  · exact alB.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)

theorem span_single {β E : Type} [DecidableEq β] [AddCommGroup E] [Module O E] (M : β → Submodule O E) (T : Finset β)
    (hM : ∀ b, b ∉ T → M b = ⊥) (n : β → ℕ) (al : ∀ b, Fin (n b) → E)
    (hspan : ∀ b, Submodule.span O (Set.range (al b)) = M b) :
    Submodule.span O (Set.range fun x : (Σ b : {b // b ∈ T}, Fin (n b.1)) =>
      (Pi.single x.1.1 (al x.1.1 x.2) : β → E)) = Submodule.pi Set.univ M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    beta_reduce
    by_cases h : i = x.1.1
    · subst h
      rw [Pi.single_eq_same, ← hspan]
      exact Submodule.subset_span ⟨x.2, rfl⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  · intro f hf
    rw [Submodule.mem_pi] at hf
    have hfT : f = ∑ b ∈ T, Pi.single b (f b) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_pi_single]
      split_ifs with hi
      · rfl
      · have h0 := hf i (Set.mem_univ i)
        rw [hM i hi, Submodule.mem_bot] at h0
        exact h0
    rw [hfT]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hfb : f b ∈ Submodule.span O (Set.range (al b)) := by
      rw [hspan]
      exact hf b (Set.mem_univ b)
    have e : (Pi.single b (f b) : β → E) = LinearMap.single O (fun _ : β => E) b (f b) := rfl
    rw [e]
    have hmap := Submodule.mem_map_of_mem (f := LinearMap.single O (fun _ : β => E) b) hfb
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨⟨b, hb⟩, i⟩, rfl⟩

end Gen

def BlockFGAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] (s : ℕ) (S : SegData s)
    (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) (w : O), Irreducible w → w ^ 2 = (p : O) →
    Module.Finite O (blockLat O p r S aTop aPlus m b)

open Classical in

theorem smithData_seg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] {s : ℕ}
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (hFG : ∀ b, Module.Finite O (blockLat O p r S aTop aPlus m b)) :
    ∃ (n : ℕ) (al be : Fin n → SegVs O r s S.t) (β : Fin n → SegBlock s r),
      SmithData (segForm O p r S) (segLat O p r S aTop aPlus m) n al be β := by
  have hfin := kf_kept_finite p r S aTop
  set T := hfin.toFinset with hT
  have hmemT : ∀ b, b ∈ T ↔ Kept p r S aTop b := fun b => by rw [hT, Set.Finite.mem_toFinset]; rfl
  let M : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    fun b => if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥
  have hMfg : ∀ b, Module.Finite O (M b) := fun b => by
    by_cases hb : Kept p r S aTop b
    · have e : M b = blockLat O p r S aTop aPlus m b := if_pos hb
      rw [e]; exact hFG b
    · have e : M b = ⊥ := if_neg hb
      rw [e]; infer_instance
  have hM0 : ∀ b, b ∉ T → M b = ⊥ := fun b hb => if_neg fun h => hb ((hmemT b).2 h)
  choose n al be hmem horth hli hsa hsb using fun b => smith_block (M b) (hMfg b)
  let ι := Σ b : {b // b ∈ T}, Fin (n b.1)
  let ev : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let AL : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (al x.1.1 x.2)
  let BE : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (be x.1.1 x.2)
  have hL : segLat O p r S aTop aPlus m = Submodule.pi Set.univ M := rfl
  have hALs : Submodule.span O (Set.range AL) = Submodule.pi Set.univ M := span_single M T hM0 n al hsa
  have hBEs : Submodule.span O (Set.range BE) = Submodule.pi Set.univ M := span_single M T hM0 n be hsb
  refine ⟨Fintype.card ι, AL ∘ ev.symm, BE ∘ ev.symm, fun i => (ev.symm i).1.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hL, ← hALs]
    refine ⟨Submodule.subset_span ⟨_, rfl⟩, ?_⟩
    rw [hALs, ← hBEs]
    exact Submodule.subset_span ⟨_, rfl⟩
  · intro i b hb
    exact ⟨Pi.single_eq_of_ne hb _, Pi.single_eq_of_ne hb _⟩
  · intro i l hil
    set x := ev.symm i with hx
    set y := ev.symm l with hy
    have hxy : x ≠ y := fun h => hil (ev.symm.injective h)
    show segForm O p r S (AL x) (BE y) = 0
    rw [segForm_eq_sum p r S {x.1.1} (AL x) (BE y) (fun b hb => Pi.single_eq_of_ne (by simpa using hb) _),
      Finset.sum_singleton]
    show _ * fock ((Pi.single x.1.1 (al x.1.1 x.2) : SegVs O r s S.t) x.1.1)
      ((Pi.single y.1.1 (be y.1.1 y.2) : SegVs O r s S.t) x.1.1) = 0
    rw [Pi.single_eq_same]
    by_cases hb : x.1.1 = y.1.1
    · obtain ⟨⟨xb, hxb⟩, xi⟩ := x
      obtain ⟨⟨yb, hyb⟩, yi⟩ := y
      simp only at hb
      subst hb
      rw [Pi.single_eq_same, horth xb xi yi (fun h => hxy (by rw [h])), mul_zero]
    · rw [Pi.single_eq_of_ne hb, fock_zero_right, mul_zero]
  · have h1 := Pi.linearIndependent_single (R := O) al hli
    have hj : Function.Injective (fun x : ι => (⟨x.1.1, x.2⟩ : Σ b, Fin (n b))) := by
      rintro ⟨⟨xb, hxb⟩, xi⟩ ⟨⟨yb, hyb⟩, yi⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      rw [eq_of_heq h2]
    exact (h1.comp _ hj).comp _ ev.symm.injective
  · rw [hL, ← hALs, EquivLike.range_comp]
  · rw [hL, ← hBEs, EquivLike.range_comp]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem wdim_shift {r : ℕ} (lam : Fin r → ℤ) (c : ℤ) : wdim (fun i => lam i + c) = wdim lam := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · congr 1
    push_cast
    ring
  · rfl

theorem wdim_nat {r : ℕ} (nu : Fin r → ℕ) :
    wdim (fun i => (nu i : ℤ)) = ∏ i : Fin r, ∏ j : Fin r,
      if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1 := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Int.cast_natCast]

theorem antitone_of_interlace {r : ℕ} {lamN : Fin (r + 1) → ℕ} (hl : Antitone lamN) (nu : Fin r → ℕ)
    (h : ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) : Antitone nu := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have h1 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      have : (i : ℕ) < (j : ℕ) := hlt
      simpa using this
    exact ((h j).2.trans (hl h1)).trans (h i).1

theorem numBranch_of {D : Formalism.BasicNotions.D7} (h2 : adm2 D) (h3 : adm3 D) : NumBranchAt := by
  intro r mu hmu
  classical
  set c : ℤ := mu (Fin.last r) with hc
  let lamN : Fin (r + 1) → ℕ := fun i => (mu i - c).toNat
  have hge : ∀ i, c ≤ mu i := fun i => hmu (Fin.le_last i)
  have hcast : ∀ i, (lamN i : ℤ) = mu i - c := fun i => Int.toNat_of_nonneg (by linarith [hge i])
  have hanti : Antitone lamN := by
    intro i j hij
    have h1 := hmu hij
    have : (lamN j : ℤ) ≤ (lamN i : ℤ) := by rw [hcast, hcast]; linarith
    exact_mod_cast this
  have e1 : wdim mu = (Module.finrank ℚ (Formalism.GradedWeylDivisibility.dualWeyl ℚ (r + 1) (r + 1) lamN) : ℚ) := by
    have hmu' : mu = fun i => (lamN i : ℤ) + c := funext fun i => by rw [hcast]; ring
    calc wdim mu = wdim (fun i => (lamN i : ℤ) + c) := congrArg wdim hmu'
      _ = wdim (fun i => (lamN i : ℤ)) := wdim_shift _ c
      _ = _ := by rw [wdim_nat, h3 ℚ (r + 1) lamN hanti]
  rw [e1, h2 ℚ r lamN hanti]
  push_cast
  set F := (Fintype.piFinset (fun _ : Fin r => Finset.range (lamN 0 + 1))).filter
    (fun nu => ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) with hF
  have hinj : Set.InjOn (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c) F := by
    intro a _ b _ hab
    funext i
    have := congrFun hab i
    simp only at this
    omega
  rw [finsum_eq_sum_of_support_subset (s := F.image (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c))]
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [hF, Finset.mem_filter] at hnu
    have hnu2 := hnu.2
    have hA : Antitone nu := antitone_of_interlace hanti nu hnu2
    rw [if_pos, wdim_shift, wdim_nat, h3 ℚ r nu hA]
    intro i
    show mu i.succ ≤ (nu i : ℤ) + c ∧ (nu i : ℤ) + c ≤ mu i.castSucc
    have h1 := hnu2 i
    have a1 := hcast i.succ
    have a2 := hcast i.castSucc
    constructor <;> omega
  · intro lam hlam
    rw [Function.mem_support] at hlam
    have hcond : ∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc := by
      by_contra hn
      exact hlam (if_neg hn)
    rw [Finset.coe_image]
    refine ⟨fun i => (lam i - c).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, hF, Finset.mem_filter, Fintype.mem_piFinset]
      have hl : ∀ i, ((lam i - c).toNat : ℤ) = lam i - c := fun i =>
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [Finset.mem_range]
        show (lam i - c).toNat < lamN 0 + 1
        have a0 := hcast 0
        have h0 : mu i.castSucc ≤ mu 0 := hmu (Fin.zero_le _)
        have := hl i
        have := (hcond i).2
        omega
      · show lamN i.succ ≤ (lam i - c).toNat ∧ (lam i - c).toNat ≤ lamN i.castSucc
        have a1 := hcast i.succ
        have a2 := hcast i.castSucc
        have b1 := hl i
        have b2 := hcond i
        constructor <;> omega
    · funext i
      have : ((lam i - c).toNat : ℤ) = lam i - c :=
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      simp only [this]
      ring

theorem stWeylAt (D : Formalism.BasicNotions.D7) : StWeylAt := by
  intro n N LL B P
  have h := Formalism.MainNotions.G.Joints.Lit.weyl_dimension_formula_index_sets D n N P.mu (P.dom (Fin.last N))
  rw [h]
  rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end

