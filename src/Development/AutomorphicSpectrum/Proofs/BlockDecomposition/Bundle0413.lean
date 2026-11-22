import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0401
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGenerated
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.SerreBpf

open GlobalTheory.QCoh GlobalTheory.Twist CechPic GlobalTheory.LB in

theorem eventually_basePointFree (Y : Var ℂ) (i : Fin (Y.N + 1))
    (hi : Y.ι (genericPoint Y.X) ∈ ProjSpace.chart ℂ Y.N i) (Δ : Y.Dv) :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ (L : LB Y.X) (r : L.ι → Y.Fnˣ) (n : ℕ) (b : Fin n → L.Sec),
      L.IsLB ∧ Presents (Δ + m • Y.hyp hi) L r ∧ ⨆ j, nonzeroLocus (b j) = ⊤ := by
  have hA : GlobalTheory.IsAmpleLB Y.O1 := Y.isAmple_projective_O_one
  have hK : (GlobalTheory.Cartier.toLB (-Δ)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have hL0 : (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))).IsLB := GlobalTheory.CechPic.isLB_dual hK
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL0
  haveI := GlobalTheory.LB.isFiniteType_toMod hL0
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) :=
    GlobalTheory.QCoh.IsFiniteQC.of_isFiniteType
  filter_upwards [hA.eventually_isGloballyGenerated_twist
    (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))] with m hm
  have hM : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb Y.isLineBundle_twistingSheafOne _ _
  have hN : (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have h1 : GlobalTheory.QCoh.IsGloballyGenerated
      (GlobalTheory.twist (GlobalTheory.twist (GlobalTheory.LB.unitMod Y.X) (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)) := by
    haveI : Epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
        (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv) :=
      (GlobalTheory.Twist.epi_map_iff hM _).2 inferInstance
    exact hm.of_epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv)
  have hiso : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      ((GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).div (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) := by
    rw [← GlobalTheory.CechPic.tens_eq_div, ← GlobalTheory.CechPic.cls_eq_iff hM (GlobalTheory.CechPic.isLB_tens hN hK),
      GlobalTheory.CechPic.cls_tens hN hK, GlobalTheory.CechPic.cls_lbPow Y.isLineBundle_twistingSheafOne, ← GlobalTheory.Cartier.toPic_apply,
      ← GlobalTheory.Cartier.toPic_apply, ← (Y.presents_hyp hi).toPic_eq, map_add, map_neg, map_nsmul]
    abel
  obtain ⟨e⟩ := GlobalTheory.Twist.nonempty_twistTwistIso (F := GlobalTheory.LB.unitMod Y.X) hL0 hM hN hiso
  have h2 : GlobalTheory.QCoh.IsGloballyGenerated (GlobalTheory.LB.toMod (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi))) :=
    (GlobalTheory.QCoh.isGloballyGenerated_iff_of_iso (e ≪≫ GlobalTheory.Twist.unitTwistIso _)).1 h1
  obtain ⟨n, s, hs⟩ := ((GlobalTheory.isGloballyGenerated_toMod_iff hN).1 h2).exists_fin_succ
  exact ⟨_, _, n + 1, s, hN, GlobalTheory.Cartier.presents_toLB _, hs⟩

end GlobalTheory.CompanionTheory.SerreBpf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmodule
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGuCore

theorem not_inf_le_of_rank_quotient_le_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (T A C : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hmod : (A ⊔ C) ⊓ T ≤ A ⊓ T ⊔ C ⊓ T) (hA : ¬ A ≤ T) (hC : ¬ C ≤ T) :
    ¬ A ⊓ C ≤ T := by
  obtain ⟨a, haA, haT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨c, hcC, hcT⟩ := SetLike.not_le_iff_exists.mp hC
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  obtain ⟨t, ht⟩ := hv₀ (Submodule.Quotient.mk c)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply haT
    rw [← Submodule.Quotient.mk_eq_zero T, ← hs, zero_smul]
  have hdiff : c - (t * s⁻¹) • a ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero T, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← hs, ← ht, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self]
  have hsum : c - (t * s⁻¹) • a ∈ A ⊔ C :=
    Submodule.sub_mem _ (Submodule.mem_sup_right hcC)
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ haA))
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmod (Submodule.mem_inf.mpr ⟨hsum, hdiff⟩))
  rw [Submodule.mem_inf] at hx hy
  have hw : c - y = (t * s⁻¹) • a + x := by
    calc c - y = (c - (t * s⁻¹) • a - (x + y)) + (t * s⁻¹) • a + x := by abel
      _ = (t * s⁻¹) • a + x := by rw [hxy, sub_self, zero_add]
  have hwA : c - y ∈ A := hw ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ haA) hx.1
  have hwC : c - y ∈ C := Submodule.sub_mem _ hcC hy.1
  intro h
  apply hcT
  have hwT : c - y ∈ T := h (Submodule.mem_inf.mpr ⟨hwA, hwC⟩)
  simpa using Submodule.add_mem _ hwT hy.2

theorem gen_core_meet {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (A C : Subrepresentation ρ)
    (hmod : (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T)
    (hA : ¬ A.toSubmodule ≤ T) (hC : ¬ C.toSubmodule ≤ T) :
    ¬ (A ⊓ C).toSubmodule ≤ T := by
  rw [Subrepresentation.toSubmodule_sup] at hmod
  rw [Subrepresentation.toSubmodule_inf]
  exact GlobalTheory.CompanionTheory.RgGuCore.not_inf_le_of_rank_quotient_le_one T A.toSubmodule C.toSubmodule hT hmod hA hC

end GlobalTheory.CompanionTheory.RgGuCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
section
noncomputable section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.PairMult

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Pos n

abbrev Cq (n : ℕ) (V : Type) : Type := Finset (Lt n) → V

def keyL (l : Lt n) : ℕ := (if l.1 then 0 else (n + 1) * (n + 1)) + CompanionTheory.D.LK.key l.2

def sgL (l : Lt n) (A : Finset (Lt n)) : ℂ := (-1) ^ (A.filter fun j => keyL j < keyL l).card

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then 0 else sgL l A • x (insert l A)
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def creq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then sgL l A • x (A.erase l) else 0
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def liftq (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cq n V →ₗ[ℂ] Cq n V' :=
  T.compLeft (Finset (Lt n))

def Ts (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ V :=
  if s then E1 p q + E2 p q else E1 p q - E2 p q

def Tl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (l : Lt n) : Module.End ℂ V := Ts E1 E2 l.1 l.2.1.1 l.2.1.2

def bdq (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ l : Lt n, (liftq n (Tl E1 E2 l) : Module.End ℂ (Cq n V)) * annq l) +
    ∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then creq ((s == t), k) * annq (t, j) * annq (s, i) else 0

def SuppQ (P : Lt n → Prop) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → ∀ l ∈ A, P l

def DegQ (j : ℕ) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → A.card = j

def adLq (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n, CompanionTheory.RgExh.U.adC p q i k • (creq ((s == t), k) * annq (t, i))

def lFq (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  liftq n (Ts E1 E2 s p q) + adLq s p q

def c1 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q + lFq E1 E2 false p q)

def c2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q - lFq E1 E2 false p q)

end Chains

abbrev inUL (lev : Fin n → ℕ) (l : Lt n) : Prop := lev l.2.1.1 < lev l.2.1.2

abbrev inKU (lev : Fin n → ℕ) (l : Lt n) : Prop := l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def omQ (lev : Fin n → ℕ) : Finset (Lt n) := univ.filter fun l => l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def topq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (v : V) : Cq n V := Pi.single (omQ lev) v

def IsSubL (lev : Fin n → ℕ) (S : Lt n → Prop) : Prop :=
  (∀ l, S l → inUL lev l) ∧ ∀ (s t : Bool) (i j k : Pos n), i.1.2 = j.1.1 → k.1.1 = i.1.1 → k.1.2 = j.1.2 →
    S (s, i) → S (t, j) → S ((s == t), k)

section Algebra

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def PairRel (E1 E2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  GlRel E1 ∧ GlRel E2 ∧ ∀ a b c d, Commute (E1 a b) (E2 c d)

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ W) : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if x.1 then E1 x.2.1 x.2.2 else E2 x.2.1 x.2.2

def evB (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if lev x.2.1 = lev x.2.2 then (if x.1 then X1 x.2.1 x.2.2 else X2 x.2.1 x.2.2) else 0

def LRel (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X1 p q * X1 r v - X1 r v * X1 p q = (if q = r then X1 p v else 0) - (if v = p then X1 r q else 0)) ∧
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X2 p q * X2 r v - X2 r v * X2 p q = (if q = r then X2 p v else 0) - (if v = p then X2 r q else 0)) ∧
  ∀ p q r v, lev p = lev q → lev r = lev v → Commute (X1 p q) (X2 r v)

def blk (lev : Fin n → ℕ) {M : ℕ} (h : ∑ i, GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i = n) (X : Fin n → Fin n → Module.End ℂ W)
    (i : Fin M) (p q : Fin (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i)) : Module.End ℂ W :=
  X (GlobalTheory.SmGL.stdBlocks (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M) h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M) h ⟨i, q⟩)

end Algebra

def Inv2 (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def InvLev (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ p q, lev p = lev q → Commute (X1 p q + X2 p q) (evB lev X1 X2 b)

def injL (s : Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => FreeAlgebra.ι ℂ (s, p)

def LiftInv : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    (∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ v w : V, v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a, Inv2 a ∧ ev2 E1 E2 a v = w

def HCDec2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → Inv2 a →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 → ∀ x : V, ∃ w : Lt n → V,
        ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0

def GenCOU2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (S : Lt n → Prop) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → IsSubL lev S →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      (∀ l, S l → Commute (Tl E1 E2 l) (ev2 E1 E2 a)) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ∀ (j : ℕ) (x : Cq n V), SuppQ S x → DegQ j x → bdq E1 E2 x = 0 →
        ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
          liftq n (ev2 E1 E2 a) x - evB lev (c1 E1 E2) (c2 E1 E2) b x = bdq E1 E2 w

def TopCyc : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    PairRel E1 E2 → ∀ v : V, (∀ l, inKU lev l → Tl E1 E2 l v = 0) → bdq E1 E2 (topq lev v) = 0

def InjectiveWedgeHighestCoefficient : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (u : V) (y : Cq n V), u ∈ hwSp E1 E2 (muQ lam lev) → SuppQ (inUL lev) y →
        DegQ ((omQ lev).card + 1) y → bdq E1 E2 y = topq lev u → u = 0

def KlChar : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ x ∈ hwSp E1 E2 (muQ lam lev), ∀ p q, lev p = lev q →
        lFq E1 E2 true p q (topq lev x) =
          if p = q then ((muQ lam lev p + 2 * rhoU lev p : ℝ) : ℂ) • topq lev x else 0

def LeviRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → PairRel E1 E2 → ∀ x : Cq n V, SuppQ (inUL lev) x →
      (∀ s p q, lev p = lev q → SuppQ (inUL lev) (lFq E1 E2 s p q x) ∧ (∀ j, DegQ j x → DegQ j (lFq E1 E2 s p q x)) ∧
        lFq E1 E2 s p q (bdq E1 E2 x) = bdq E1 E2 (lFq E1 E2 s p q x)) ∧
      ∀ p q r v, lev p = lev q → lev r = lev v →
        (c1 E1 E2 p q (c1 E1 E2 r v x) - c1 E1 E2 r v (c1 E1 E2 p q x) =
          (if q = r then c1 E1 E2 p v x else 0) - (if v = p then c1 E1 E2 r q x else 0)) ∧
        (c2 E1 E2 p q (c2 E1 E2 r v x) - c2 E1 E2 r v (c2 E1 E2 p q x) =
          (if q = r then c2 E1 E2 p v x else 0) - (if v = p then c2 E1 E2 r q x else 0)) ∧
        c1 E1 E2 p q (c2 E1 E2 r v x) = c2 E1 E2 r v (c1 E1 E2 p q x)

def InvL : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W)
    (L : Submodule ℂ W) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), LRel lev X1 X2 →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) s ∈ L) →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) (evB lev X1 X2 b s) = evB lev X1 X2 b ((X1 p q + X2 p q) s)) →
    ∃ b', InvLev lev b' ∧ ∀ s ∈ L, evB lev X1 X2 b' s = evB lev X1 X2 b s

def CenterScalar : Prop :=
  ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    ∀ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), InvLev lev b → ∀ τ : Fin n → ℂ, (∀ a c, lev a = lev c → τ a = τ c) →
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
        ∀ t : W, (∀ p q, lev p = lev q → (X1 p q + X2 p q) t = if p = q then τ p • t else 0) →
          (∀ (i : Fin M) (u : ℂ), ∃ g : ℂ, qdet (blk lev h X1 i) u t = g • t) → ∃ s : ℂ, evB lev X1 X2 b t = s • t

def BlockSplit : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (t : W) (n M : ℕ) (lev : Fin n → ℕ) (L : Fin n → ℝ)
    (A B : ∀ i : Fin M, Fin (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i) → Fin (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i) → Module.End ℂ W)
    (s τ : Fin M → ℂ), t ≠ 0 → Monotone lev → (∀ a, lev a < M) → StrictAnti L → (∀ i, GlRel (A i)) → (∀ i, GlRel (B i)) →
    (∀ i j, i ≠ j → ∀ p q r v, Commute (A i p q) (A j r v)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (B i p q) (B j r v)) →
    (∀ i j p q r v, Commute (A i p q) (B j r v)) →
    (∀ Y : ℂ, (List.ofFn fun i => qdet (A i) (Y + s i)).prod = Formalism.QuantumDeterminants.capP (fun a => (L a : ℂ)) Y • (1 : Module.End ℂ W)) →
    (∀ Y : ℂ, (List.ofFn fun i => qdet (B i) (Y + s i)).prod = Formalism.QuantumDeterminants.capP (fun a => (L a : ℂ)) Y • (1 : Module.End ℂ W)) →
    (∀ i, (∑ p, (A i p p + B i p p)) t = τ i • t) →
    (∀ i : Fin M, τ i = 2 * ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (L a : ℂ) +
      (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i : ℂ) * ((GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i : ℂ) - 1) - 2 * (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i : ℂ) * s i) →
    ∀ (i : Fin M) (Y : ℂ), qdet (A i) (Y + s i) t = (∏ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (Y + (L a : ℂ))) • t

def CapOne : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA E m x = GlobalTheory.Dec.gelfVal χ m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

def DualCap : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA (barF E) m x = GlobalTheory.Dec.gelfVal (fun a => -χ a) m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

def CapProd : Prop :=
  ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ∀ (s : Bool) (Y r : ℂ), qdet (if s then E1 else E2) (Y + ((n : ℂ) - 1) / 2) = r • (1 : Module.End ℂ V) →
        ∀ (j : ℕ) (x : Cq n V), SuppQ (inUL lev) x → DegQ j x → bdq E1 E2 x = 0 →
          ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
            r • x - evB lev (c1 E1 E2) (c2 E1 E2) (injL s (GlobalTheory.CompanionTheory.RgCOBlock.fb (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M) h Y)) x = bdq E1 E2 w

def LeviScalar : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v w : V, v ∈ hwSp E1 E2 (muQ lam lev) → w ∈ hwSp E1 E2 (muQ lam lev) → v ≠ 0 →
        ∀ b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
          (∃ y : Cq n V, SuppQ (inUL lev) y ∧ DegQ ((omQ lev).card + 1) y ∧
            topq lev w - evB lev (c1 E1 E2) (c2 E1 E2) b (topq lev v) = bdq E1 E2 y) →
          ∃ (s : ℂ) (y : Cq n V), SuppQ (inUL lev) y ∧ DegQ ((omQ lev).card + 1) y ∧
            topq lev w - s • topq lev v = bdq E1 E2 y

end GlobalTheory.CompanionTheory.PairMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.ChernPoly

theorem inter_add_nsmul_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv), ∃ Q : Polynomial ℝ, ∀ m : ℕ,
      ((Y.inter fun _ => Δ + m • Δ₀ : ℤ) : ℝ) = Q.eval (m : ℝ) := by
  intro Y Δ Δ₀
  classical
  refine ⟨∑ s : Finset (Fin Y.dim),
    Polynomial.C ((Y.interForm (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) : ℤ) : ℝ) * Polynomial.X ^ s.card,
    fun m => ?_⟩
  have h1 : (fun _ : Fin Y.dim => Δ + m • Δ₀) = (fun _ => (m : ℤ) • Δ₀) + (fun _ => Δ) := by
    funext i
    rw [Pi.add_apply, natCast_zsmul, add_comm]
  rw [← Y.interForm_apply, h1, MultilinearMap.map_add_univ]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : (s.piecewise (fun i => (m : ℤ) • s.piecewise (fun _ => Δ₀) (fun _ => Δ) i)
      (s.piecewise (fun _ => Δ₀) (fun _ => Δ))) = s.piecewise (fun _ => (m : ℤ) • Δ₀) (fun _ => Δ) := by
    funext i
    by_cases hi : i ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hi,
        Finset.piecewise_eq_of_mem _ _ _ hi]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi,
        Finset.piecewise_eq_of_notMem _ _ _ hi]
  have key := Y.interForm.map_piecewise_smul (fun _ => (m : ℤ)) (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) s
  rw [hpw, Finset.prod_const, smul_eq_mul] at key
  rw [key]
  push_cast
  ring

end GlobalTheory.CompanionTheory.ChernPoly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientsEquivOfNotLe
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_quotient_of_eq {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P Q : Submodule ℂ W)
    (hP : ∀ g, P ≤ P.comap (σ g)) (hQ : ∀ g, Q ≤ Q.comap (σ g)) (h : P = Q) :
    Nonempty ((σ.quotient P hP).Equiv (σ.quotient Q hQ)) := by
  subst h
  exact ⟨Representation.Equiv.mk' (Representation.IntertwiningMap.id _) id
    (fun _ => rfl) (fun _ => rfl)⟩

theorem eq_or_eq_top_of_isIrreducible_quotient {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P : Submodule ℂ W) (hP : ∀ g, P ≤ P.comap (σ g))
    (hirr : (σ.quotient P hP).IsIrreducible) (M : Submodule ℂ W)
    (hM : ∀ g, M ≤ M.comap (σ g)) (hPM : P ≤ M) : M = P ∨ M = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation (σ.quotient P hP)) := hirr
  let N : Subrepresentation (σ.quotient P hP) :=
    ⟨M.map P.mkQ, by
      rintro g _ ⟨m, hm, rfl⟩
      exact ⟨σ g m, hM g hm, rfl⟩⟩
  let S₀ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊥, by
      intro g v hv
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]⟩
  let S₁ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊤, by
      intro _ _ _
      exact Submodule.mem_top⟩
  have hcomap : (M.map P.mkQ).comap P.mkQ = M := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hPM]
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · left
    have h1 : N ⊓ S₀ = N := by rw [hN, bot_inf_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_inf] at h2
    have h3 : M.map P.mkQ = ⊥ := le_bot_iff.mp (inf_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_bot, Submodule.ker_mkQ]
  · right
    have h1 : N ⊔ S₁ = N := by rw [hN, top_sup_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_sup] at h2
    have h3 : M.map P.mkQ = ⊤ := top_le_iff.mp (sup_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_top]

theorem nonempty_equiv_subQuot (ρ : Representation ℂ G V) (E K L : Subrepresentation ρ)
    (hK : (subQuot E K).IsIrreducible) (hL : (subQuot E L).IsIrreducible)
    (hE : ¬ E ≤ E ⊓ K ⊔ E ⊓ L) : Nonempty ((subQuot E K).Equiv (subQuot E L)) := by
  have hPK : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact K.2 g hx
  have hPL : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact L.2 g hx
  have hK' : (E.toRepresentation.quotient _ hPK).IsIrreducible := hK
  have hL' : (E.toRepresentation.quotient _ hPL).IsIrreducible := hL
  have hsup : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    exact sup_le ((hPK g).trans (Submodule.comap_mono le_sup_left))
      ((hPL g).trans (Submodule.comap_mono le_sup_right))
  have hsup' : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    rw [sup_comm]
    exact hsup g
  have hne : K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    intro htop
    apply hE
    have hle : E.toSubmodule ≤ E.toSubmodule ⊓ K.toSubmodule ⊔ E.toSubmodule ⊓ L.toSubmodule := by
      intro x hx
      have hmem : (⟨x, hx⟩ : E.toSubmodule) ∈
          K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      exact Submodule.mem_sup.mpr ⟨y, ⟨y.2, hy⟩, z, ⟨z.2, hz⟩, congrArg Subtype.val hyz⟩
    rw [← inf_eq_left]
    apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_sup,
      Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_inf]
    exact inf_eq_left.mpr hle
  have hne' : L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    rw [sup_comm]
    exact hne
  have h1 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPK hK' _ hsup le_sup_left).resolve_right hne
  have h2 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPL hL' _ hsup' le_sup_left).resolve_right hne'
  have hPQ : K.toSubmodule.comap E.toSubmodule.subtype = L.toSubmodule.comap E.toSubmodule.subtype :=
    le_antisymm (sup_eq_left.mp h2) (sup_eq_left.mp h1)
  exact GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_quotient_of_eq E.toRepresentation _ _ hPK hPL hPQ

end GlobalTheory.CompanionTheory.GenCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquivFoundationStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_equiv_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), ∃ e : Jacquet π (unipRad k (stdBlocks d hd)) ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.JacquetModule k N (Zl.JC.blockIdx d hd) π, (∀ v : V, e (Submodule.Quotient.mk v) = Representation.Coinvariants.mk _ v) ∧ ∀ (g : Levi k (fun a => Fin (d a))) (hg : leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd)) (x : Jacquet π (unipRad k (stdBlocks d hd))), e (jacU (stdBlocks d hd) π g x) = GroundTheory.Automorphic.Parabolic.jacquetAction k N (Zl.JC.blockIdx d hd) π ⟨_, hg⟩ (e x) := by
  first | exact @GlobalTheory.CompanionTheory.JacquetDict.jacquet_stdBlocks_equiv | exact GlobalTheory.CompanionTheory.JacquetDict.jacquet_stdBlocks_equiv | (intros; apply GlobalTheory.CompanionTheory.JacquetDict.jacquet_stdBlocks_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEqStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_character_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.MirCharEq k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | exact GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | (intros; apply GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single <;> assumption)
end

