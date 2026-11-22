import Formalism.SharpRestriction.InertJacobiLevels.EtaSz
import Formalism.SharpRestriction.GrowthBounds.DefsInst
import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldSatisfiesConditions

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.AsmKap
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G

def gdOf (R : Ranks) : GC.GD := ⟨R, ⟨∅, ∅, 0, fun _ => PrimeClass.splitK⟩, fun _ => 0⟩

def glOf (R : Ranks) (sc : Scale) (Sc eta : ℝ) : GC.GParameters (gdOf R) := ⟨sc, Sc, eta⟩

def epOf (Ce : ℝ) (R : Ranks) (sc : Scale) : ℕ → ℕ :=
  fun p => ⌈Ce * (R.f : ℝ) * (R.k : ℝ) ^ 2 * Real.logb p sc.a⌉₊

def kapSetV (R : Ranks) (sc : Scale) (Sc : ℝ) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    Set ℝ :=
  {κ | 0 ≤ κ ∧
    ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
      [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
      (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
      UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
      ∀ lam0 : Fin n' → Fin (R.k - 1 + 1) → ℤ, IsBaseWeight TT a b ⌊4 * Sc⌋₊ lam0 → IsDominant lam0 →
        LPprime (W := W) p n' ι σ w 1 lam0 ⌈GC.tIf K (glOf R sc Sc 0) p n' TT a b⌉₊ (GC.DIf K (glOf R sc Sc 0) p n') κ
          (8 * (GC.DIf K (glOf R sc Sc 0) p n' + 1))}

def kapIOf (R : Ranks) (sc : Scale) (Sc : ℝ) (K : Consts) : KapI :=
  fun p n' TT a b => sInf (kapSetV R sc Sc K p n' TT a b)

theorem kapISet_eq {D : D7} (L : SizeData₂ D) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    kapISet L K p n' TT a b = kapSetV D.R L.sc L.Sc K p n' TT a b := rfl

theorem defs_of_shared {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : Consts) (Ce : ℝ) {R : Ranks} {sc : Scale}
    {Sc : ℝ} (hR : D.R = R) (hsc : L.sc = sc) (hSc : L.Sc = Sc) (hep : X.ep = epOf Ce R sc)
    (hk : X.kapI = kapIOf R sc Sc K) : EpDef X Ce ∧ KapIDef X K := by
  subst hR hsc hSc
  exact ⟨fun p => by rw [hep]; rfl, fun p n' TT a b => by rw [hk, kapISet_eq]; rfl⟩

theorem TieHyp.defs {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {C : FC} {R : Ranks} {sc : Scale} {Sc : ℝ}
    (H : TieHyp gatT L0 (kapIOf R sc Sc C.GK) (epOf C.cX.Ce R sc)) (hR : D.R = R) (hsc : L0.sc = sc)
    (hSc : L0.Sc = Sc) (Λ : LatIn D) : EpDef (H.Gx C.GK C.Cr Λ) C.cX.Ce ∧ KapIDef (H.Gx C.GK C.Cr Λ) C.GK :=
  defs_of_shared (H.Gx C.GK C.Cr Λ) C.GK C.cX.Ce hR hsc hSc rfl rfl

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.AsmRec
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

abbrev Core : Type 1 := Σ R : Ranks, Host R × (↥(R.Psi) → HCParam R)

def coreOf (D : D7) : Core := ⟨D.R, D.host, fun g => D.hc (D.eTau.symm g)⟩

def plPsi (φ : Formalism.HC.Frame) (c : Bool) (t : φ.A) : ↥φ.Psi :=
  ⟨if c then φ.tau2 t else φ.tau1 t, by
    rw [(factPlaces φ).1]
    cases c
    · exact Or.inl ⟨t, by simp⟩
    · exact Or.inr ⟨t, by simp⟩⟩

def wjv (R : Ranks) (hc : ↥(R.Psi) → HCParam R) (j : ℕ) (c : Bool) (v : ℕ) : ℝ :=
  if h : j - 1 < R.m then (((hc (plPsi R.toFrame c (R.ofNat v))).e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

def Core.rh (X : Core) : Σ R : Ranks, Host R := ⟨X.1, X.2.1⟩

def Core.wjv (X : Core) : ℕ → Bool → ℕ → ℝ := Inhab.wjv X.1 X.2.2

theorem wj_core (D : D7) (j : ℕ) (c : Bool) (t : G.HH D) : wj D j (tauOf D (c, t)) = (coreOf D).wjv j c t.val := by
  show wj D j (tauOf D (c, t)) =
    if h : j - 1 < D.R.m then
      (((D.hc (D.eTau.symm (plPsi D.R.toFrame c (D.R.ofNat t.val)))).e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0
  rw [Formalism.HC.Frame.ofNat_val]
  rfl

def OkT {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT) (Ts : ℝ) (T : ℕ) : Prop :=
  T.Prime ∧ Ts ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts ∧ TNorm (host2 B 0 ∅) T ∧ T ≠ B.pde ∧ T ≠ B.pde'

def GeneratorPrimeEtaBound (Ts : ℝ) (T : ℕ) (Y : Σ R : Ranks, Host R) : Prop :=
  T.Prime ∧ Ts ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + 1 / ((Y.1.f : ℝ) * Y.1.k)) * Ts ∧ TNorm Y.2 T ∧ T ≠ Y.2.pde ∧ T ≠ Y.2.pde'

def inertBaseShadowData {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT) (etaSz Sc : ℝ) (offS : ℕ → ℕ → ℝ) (kapI : KapI)
    (ep : ℕ → ℕ) : Shd0 where
  R := R
  TTn := B.TT.image Formalism.HC.Frame.A.val
  T2 := B.T2
  q := B.q
  d := B.d
  g := ![B.g0, B.g1]
  pde := B.pde
  pde' := B.pde'
  bits := fun _ => false
  etaSz := etaSz
  Sc := Sc
  hP := (fieldDataH ⟨R, host2 B 0 ∅⟩).hval
  offS := offS
  kapI := kapI
  ep := ep

end Formalism.MainNotions.Inhab

end
end

