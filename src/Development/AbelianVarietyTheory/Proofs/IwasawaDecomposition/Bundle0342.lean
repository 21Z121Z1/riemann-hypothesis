import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLog
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ValGroup

theorem exists_log {K : Type} [Field K] (w : AbsoluteValue K ℝ) (x : K) :
    ∃ a : K, a ≠ 0 ∧ Real.log (w x) = Real.log (w a) := by
  by_cases h : x = 0
  · exact ⟨1, one_ne_zero, by simp [h]⟩
  · exact ⟨x, h, rfl⟩

theorem exists_log_sub {K : Type} [Field K] (w : AbsoluteValue K ℝ) (x x' : K) :
    ∃ a : K, a ≠ 0 ∧ Real.log (w x') - Real.log (w x) = Real.log (w a) := by
  obtain ⟨a, ha, h⟩ := exists_log w x
  obtain ⟨b, hb, h'⟩ := exists_log w x'
  refine ⟨b / a, div_ne_zero hb ha, ?_⟩
  rw [h, h', map_div₀, Real.log_div (w.ne_zero hb) (w.ne_zero ha)]

theorem nonempty_algPt {F : Type} [Field F] [NumberField F] (Y : Var F) : Nonempty (AlgPt Y) := by
  have hP : IsProper Y.str := by
    have := isProper_str F Y.N
    change IsProper (Y.I.subschemeι ≫ PSpace.str F Y.N)
    infer_instance
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.str
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (X := Y.X) Set.univ_nonempty
  obtain ⟨⟨y, -⟩⟩ := ((ExtConj.main F).2.1 Y x hx).1
  exact ⟨y⟩

theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L L' : HermLB M.p) (k : ℕ+) (cf cf' : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced M L' k cf' → ∀ v : HeightOneSpectrum (𝓞 F), ∃ (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 ∧ ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v) = Real.log (e.w α) := by
  intro F _ _ C Y A M L L' k cf cf' ⟨_, r, _, _, h⟩ ⟨_, r', _, _, h'⟩ v
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  obtain ⟨y⟩ := nonempty_algPt Y
  obtain ⟨yt, hyt, hU⟩ := exists_valuationRing_point F Y M v e y
  have chart (B : HermLB M.p) : ∃ i, yt (IsLocalRing.closedPoint e.O) ∈ B.B.U i :=
    Opens.mem_iSup.1 (B.isLB.cover.ge (Set.mem_univ _))
  obtain ⟨i, hi⟩ := chart L
  obtain ⟨i', hi'⟩ := chart L'
  have h₁ := h v e y yt (fun _ => i) hyt (hU _ hi).1
  have h₂ := h' v e y yt (fun _ => i') hyt (hU _ hi').1
  obtain ⟨a, ha, h₃⟩ := exists_log_sub e.w
    (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r (fun _ => i) : Y.Fnˣ) : Y.Fn))
    (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r' (fun _ => i') : Y.Fnˣ) : Y.Fn))
  refine ⟨e, a, ha, ?_⟩
  rw [← h₃]
  linarith

end GlobalTheory.TrueGeo.ValGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k m : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced M (L.pow m) (k * m) cf := by
  first | exact @GlobalTheory.TrueGeo.InducedPow.induced_pow | exact GlobalTheory.TrueGeo.InducedPow.induced_pow | (intros; apply GlobalTheory.TrueGeo.InducedPow.induced_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElementStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_shift_element : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (b : 𝓞 F), b ≠ 0 → ∀ ht : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖, A.Induced M L k cf → A.Induced M (L.shift (fun σ => Real.log ‖σ b‖) ht) k (fun v => cf v + Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) := by
  first | exact @GlobalTheory.TrueGeo.IndScale.induced_shift | exact GlobalTheory.TrueGeo.IndScale.induced_shift | (intros; apply GlobalTheory.TrueGeo.IndScale.induced_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure AlgWtM where
  d : ℕ
  ρ : Representation ℂ (GQ L n) (Fin d → ℂ)
  alg : IsAlgWeight L n ρ
  irr : ρ.IsIrreducible

structure AutRepM extends AlgWtM L n where
  S : Submodule ℂ (GAf L n → (Fin d → ℂ))
  irrS : NG.IsIrrRep ρ S

variable {L n}

def AlgWtM.toAlgWt (m : AlgWtM L n) : NG.AlgWt L n := ⟨Fin m.d → ℂ, m.ρ, m.alg, m.irr⟩

def AutRepM.toAutRep (m : AutRepM L n) : NG.AutRep L n := ⟨m.toAlgWtM.toAlgWt, m.S, m.irrS⟩

variable (L n)

def AUq : Type := {X : Set (AutRepM L n) // ∃ π : NG.AutRep L n, X = {m | π.Iso m.toAutRep}}

def WtQ : Type := {X : Set (AlgWtM L n) // ∃ a : NG.AlgWt L n, X = {m | a.Iso m.toAlgWt}}

variable {L n}

def clsA (π : NG.AutRep L n) : AUq L n := ⟨{m | π.Iso m.toAutRep}, π, rfl⟩

def clsW (a : NG.AlgWt L n) : WtQ L n := ⟨{m | a.Iso m.toAlgWt}, a, rfl⟩

def AUq.rep (X : AUq L n) : NG.AutRep L n := X.2.choose

def WtQ.rep (X : WtQ L n) : NG.AlgWt L n := X.2.choose

theorem AUq.cls_rep (X : AUq L n) : clsA X.rep = X := Subtype.ext X.2.choose_spec.symm

theorem WtQ.cls_rep (X : WtQ L n) : clsW X.rep = X := Subtype.ext X.2.choose_spec.symm

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LocAt (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) (x : GlobalTheory.LocGL.IrrGL (w.adicCompletion L)) : Prop :=
  ∃ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : s.w = w),
    IsLocS π.S s σ ∧ HEq (GlobalTheory.LocLanglands.cls σ) x

end

open Classical in

def hwOf (a : NG.AlgWt L n) (τ : L →+* ℂ) : Fin n → ℤ :=
  if h : ∃ lam, a.HWAt τ lam ∧ Antitone lam then h.choose else 0

theorem hwOf_antitone (a : NG.AlgWt L n) (τ : L →+* ℂ) : Antitone (hwOf a τ) := by
  unfold hwOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact fun _ _ _ => le_rfl

open Classical in

def satOf (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ :=
  if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAt π Dv α
  then Finset.univ.val.map h.choose_spec.choose_spec.choose else Multiset.replicate (n / 2) 1

theorem satOf_card (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset.card (satOf π w) = n / 2 := by
  unfold satOf
  split_ifs <;> simp

theorem infOf_card (lam : Fin n → ℤ) : Multiset.card (NG.infOf lam) = n := by
  simp [NG.infOf]

theorem infOf_nodup_alg {lam : Fin n → ℤ} (hl : Antitone lam) : (NG.infOf lam).Nodup ∧
    ∀ x ∈ NG.infOf lam, ∃ k : ℤ, x = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  refine ⟨?_, ?_⟩
  · unfold NG.infOf
    refine Multiset.Nodup.map_on (fun i _ j _ hij => ?_) Finset.univ.nodup
    have h1 : ((lam i - (i : ℕ) : ℤ) : ℂ) = ((lam j - (j : ℕ) : ℤ) : ℂ) := by
      push_cast; linear_combination hij
    have h2 : lam i - (i : ℕ) = lam j - (j : ℕ) := by exact_mod_cast h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hl (le_of_lt h); have : (i : ℕ) < (j : ℕ) := h; omega
    · have := hl (le_of_lt h); have : (j : ℕ) < (i : ℕ) := h; omega
  · intro x hx
    unfold NG.infOf at hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam i - (i : ℕ), by push_cast; ring⟩

end GlobalTheory.AutQuot

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

open Classical in

def locOf (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w

open Classical in

def wtOf (π : NG.AutRep D.host.E D.R.nV) : WtQ D.host.E D.R.nV :=
  if h : ∃ b, π.toAlgWt.IsDual b then clsW h.choose else clsW π.toAlgWt

set_option synthInstance.maxHeartbeats 400000 in

def nbcOf (hE : IsEmpty D.nd.Loc) : NBC D.naut where
  AU := fun _ => AUq D.host.E D.R.nV
  multAU := fun _ X => X.rep.mult
  sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ X.rep.SphAt v
  locAU := fun _ X w => locOf hL D T X.rep w
  satAU := fun _ X w => satOf X.rep w
  satAU_card := fun _ X w => satOf_card X.rep w
  Wt := fun _ => WtQ D.host.E D.R.nV
  infW := fun _ Y τ => NG.infOf (hwOf Y.rep τ)
  infW_card := fun _ Y τ => infOf_card _
  wtAU := fun _ X => wtOf D X.rep
  infW_alg := fun _ Y τ => infOf_nodup_alg (hwOf_antitone Y.rep τ)
  embAV := fun i => isEmptyElim i
  embAV_inj := fun i => isEmptyElim i
  embAV_loc := fun i => isEmptyElim i
  embAV_sat := fun i => isEmptyElim i
  embAV_sph := fun i => isEmptyElim i
  embAV_inf := fun i => isEmptyElim i

end GlobalTheory.AutQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfTypeSpaceNeBotOfIsotypicPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MoveTyped

open Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem isSubrep_bot (ρ : Representation ℂ (GQ L n) W) :
    IsSubrep ρ (⊥ : Submodule ℂ (GAf L n → W)) :=
  ⟨bot_le, fun h f hf => by
    rw [Submodule.mem_bot] at hf ⊢
    subst hf
    exact map_zero _⟩

theorem isSubrep_sup {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊔ Y) :=
  ⟨sup_le hX.le hY.le, fun h f hf => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]
    exact Submodule.add_mem_sup (hX.stable h a ha) (hY.stable h b hb)⟩

theorem isSubrep_inf {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊓ Y) :=
  ⟨inf_le_right.trans hY.le, fun h f hf => ⟨hX.stable h f hf.1, hY.stable h f hf.2⟩⟩

theorem sup_typed_eq_bot {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {X Y : Submodule ℂ (GAf L n → W)} (hX : IsSubrep ρ X) (hXT : X ⊓ TypeSp ρ J χ = ⊥)
    (hY : IsIrrRep ρ Y) (hYT : Y ⊓ TypeSp ρ J χ = ⊥) : (X ⊔ Y) ⊓ TypeSp ρ J χ = ⊥ := by
  by_cases hXY : X ⊓ Y = ⊥
  · rw [eq_bot_iff]
    rintro v ⟨hv, hvT⟩
    have hvT' : v ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) v = ((χ κ : ℂˣ) : ℂ) • v := hvT
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have key : ∀ κ : J, rt L n (κ : GAf L n) a = ((χ κ : ℂˣ) : ℂ) • a ∧
        rt L n (κ : GAf L n) b = ((χ κ : ℂˣ) : ℂ) • b := by
      intro κ
      have e := hvT'.2 κ
      rw [map_add, smul_add] at e
      have hmem : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a ∈ X ⊓ Y := by
        refine ⟨Submodule.sub_mem _ (hX.stable _ a ha) (Submodule.smul_mem _ _ ha), ?_⟩
        have hab : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a =
            ((χ κ : ℂˣ) : ℂ) • b - rt L n (κ : GAf L n) b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        rw [hab]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) (hY.1.stable _ b hb)
      rw [hXY, Submodule.mem_bot, sub_eq_zero] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at e
      exact add_left_cancel e
    have ha0 : a ∈ X ⊓ TypeSp ρ J χ := ⟨ha, hX.le ha, fun κ => (key κ).1⟩
    have hb0 : b ∈ Y ⊓ TypeSp ρ J χ := ⟨hb, hY.1.le hb, fun κ => (key κ).2⟩
    rw [hXT, Submodule.mem_bot] at ha0
    rw [hYT, Submodule.mem_bot] at hb0
    simp [ha0, hb0]
  · have hle : X ⊓ Y = Y := (hY.2.2 _ (isSubrep_inf hX hY.1) inf_le_right).resolve_left hXY
    have hYX : Y ≤ X := hle ▸ inf_le_left
    rw [sup_eq_left.2 hYX, hXT]

theorem typed_eq_bot_of_iso {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {S S' : Submodule ℂ (GAf L n → W)} (hS : IsSubrep ρ S) (hiso : IsoRep S S')
    (h : S ⊓ TypeSp ρ J χ = ⊥) : S' ⊓ TypeSp ρ J χ = ⊥ := by
  obtain ⟨T, hT⟩ := hiso
  rw [eq_bot_iff]
  rintro u ⟨hu, huT⟩
  have huT' : u ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) u = ((χ κ : ℂˣ) : ℂ) • u := huT
  obtain ⟨f, hfu⟩ : ∃ f : S, T f = ⟨u, hu⟩ := ⟨T.symm _, T.apply_symm_apply _⟩
  have hf : ∀ κ : J, rt L n (κ : GAf L n) (f : GAf L n → W) = ((χ κ : ℂˣ) : ℂ) • (f : GAf L n → W) := by
    intro κ
    let f' : S := ⟨rt L n (κ : GAf L n) f, hS.stable _ _ f.2⟩
    have e := hT κ f f' rfl
    have hTT : T f' = T (((χ κ : ℂˣ) : ℂ) • f) := by
      apply Subtype.ext
      rw [e, map_smul, Submodule.coe_smul, hfu]
      exact huT'.2 κ
    have := congrArg Subtype.val (T.injective hTT)
    simpa [f'] using this
  have hfm : (f : GAf L n → W) ∈ S ⊓ TypeSp ρ J χ := ⟨f.2, hS.le f.2, hf⟩
  rw [h, Submodule.mem_bot] at hfm
  have hf0 : f = 0 := Subtype.ext hfm
  rw [hf0, map_zero] at hfu
  have := congrArg Subtype.val hfu
  simpa using this.symm

theorem typed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S →
    Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  intro L _ _ _ n W _ _ ρ J χ S hS hne h0
  apply hne
  have hfam : ∀ S' ∈ {S' | IsIrrRep ρ S' ∧ IsoRep S S'}, S' ⊓ TypeSp ρ J χ = ⊥ :=
    fun S' hS' => typed_eq_bot_of_iso hS hS'.2 h0
  have fin : ∀ s : Finset (Submodule ℂ (GAf L n → W)), (↑s : Set _) ⊆ {S' | IsIrrRep ρ S' ∧ IsoRep S S'} →
      IsSubrep ρ (⨆ i ∈ s, i) ∧ (⨆ i ∈ s, i) ⊓ TypeSp ρ J χ = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [isSubrep_bot]
    | insert a s ha ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨h1, h2⟩ := ih hs.2
      rw [Finset.iSup_insert, sup_comm]
      exact ⟨isSubrep_sup h1 hs.1.1.1, sup_typed_eq_bot h1 h2 hs.1.1 (hfam a hs.1)⟩
  rw [eq_bot_iff]
  rintro v ⟨hv, hvT⟩
  unfold isoTyp at hv
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hv
  have hb := (fin s hs).2
  rw [eq_bot_iff] at hb
  exact hb ⟨hvs, hvT⟩

end GlobalTheory.MoveTyped
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integration_by_parts_rightDerivative_adelicQuotient : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  first | exact @GlobalTheory.Mem.IntByParts.integral_Rder_mul | exact GlobalTheory.Mem.IntByParts.integral_Rder_mul | (intros; apply GlobalTheory.Mem.IntByParts.integral_Rder_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGenericStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krullDim_one_of_finite_generic : ∀ (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z] (f : Z' ⟶ Z) [IsProper f], topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → 0 < f.residueDegree (genericPoint Z') → topologicalKrullDim Z' = 1 := by
  first | exact @GlobalTheory.ProperCover.dim_eq_one | exact GlobalTheory.ProperCover.dim_eq_one | (intros; apply GlobalTheory.ProperCover.dim_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC | exact GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC | (intros; apply GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocBrOfAutSpec
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem locBr_of_autSpec : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), AutSpec A M tup Sp.iq Y Cb → ∃ Br : LocBr Y, Br.nbr = Sp.nbr := by
  intro D cf jE A M C tup big X T Sp Y Cb hA
  refine ⟨⟨Sp.nbr, Sp.nbr_ind, Sp.self_good, ?_⟩, rfl⟩
  intro i w hw
  have hφ : ∀ x : X.nd.O i, iotaOQ X.nd Y.naut i x =
      (((Sp.nbr i w hw).toLL x : ↥(Sp.nbr i w hw).LL.1) : Loc.Om (X.nd.l i)) := by
    intro x
    show Y.naut.iotaQ i (algebraMap _ _ x) = _
    rw [hA.iotaQ i]
    exact Sp.nbr_iq i w hw x
  have hL := A.wd.loc (X.nd.l i) (Y.naut.iotaQC i) w hw (X.nd.O i) (Sp.nbr i w hw) (Sp.nbr_ind i w hw)
    (iotaOQ X.nd Y.naut i) hφ
  refine ⟨hφ, ?_, ?_⟩
  · intro m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.1 m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (iotaOQ X.nd Y.naut i) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (iotaOQ X.nd Y.naut i) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
  · intro LL' hLL m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.2 LL' hLL m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCellOfUnipotentIwahoriProduct
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IwaCell

namespace GlobalTheory.IwaCell

theorem right_translate_mem_cell (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ) (hϖ : ord k ϖ = 1) (b d : Fin m → ℤ) (hd : Monotone d) (g : GL (Fin m) k)
    (hg : ∃ u ∈ unipB k (Fin m), ∃ i ∈ iwahori k (Fin m), g * tD ϖ d = u * tD ϖ (b + d) * i) :
    g ∈ cell ϖ b := by
  obtain ⟨u, hu, i, hi, e⟩ := hg
  obtain ⟨n, hn, c, hc, l, hl, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hi
  have hl' := GlobalTheory.IwaStep.conj_mem_unipLowerOne hϖ hd hl
  have hnB : tD ϖ d * n * (tD ϖ d)⁻¹ ∈ unipB k (Fin m) := GlobalTheory.IwahoriTraceProof.conj_mem_unipB _ hn.1
  have hnB' : tD ϖ b * (tD ϖ d * n * (tD ϖ d)⁻¹) * (tD ϖ b)⁻¹ ∈ unipB k (Fin m) :=
    GlobalTheory.IwahoriTraceProof.conj_mem_unipB _ hnB
  have hK : diagT k (Fin m) c * (tD ϖ d * l * (tD ϖ d)⁻¹) ∈ KO k (Fin m) :=
    iwahori_le_KO k (Fin m) (mul_mem (diagT_mem_iwahori hc) (KOne_le_iwahori k (Fin m) hl'.2))
  have hcomm : tD ϖ d * diagT k (Fin m) c = diagT k (Fin m) c * tD ϖ d := by
    rw [tD, ← map_mul, ← map_mul, mul_comm]
  have hg : g = (u * (tD ϖ b * (tD ϖ d * n * (tD ϖ d)⁻¹) * (tD ϖ b)⁻¹)) * tD ϖ b *
      (diagT k (Fin m) c * (tD ϖ d * l * (tD ϖ d)⁻¹)) := by
    have e2 : g = u * tD ϖ (b + d) * (n * diagT k (Fin m) c * l) * (tD ϖ d)⁻¹ := by
      rw [← e]; group
    rw [e2, tD_add]
    have h3 : (tD ϖ d)⁻¹ * diagT k (Fin m) c * tD ϖ d = diagT k (Fin m) c := by
      rw [mul_assoc, ← hcomm]; group
    calc u * (tD ϖ b * tD ϖ d) * (n * diagT k (Fin m) c * l) * (tD ϖ d)⁻¹
        = u * (tD ϖ b * tD ϖ d) * (n * ((tD ϖ d)⁻¹ * diagT k (Fin m) c * tD ϖ d) * l) * (tD ϖ d)⁻¹ := by rw [h3]
      _ = _ := by group
  rw [hg]
  exact mul_mem_cell (mul_mem hu hnB') hK

example : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ (b d : Fin m → ℤ), Monotone d → ∀ g : GL (Fin m) k, (∃ u ∈ unipB k (Fin m), ∃ i ∈ iwahori k (Fin m), g * tD ϖ d = u * tD ϖ (b + d) * i) → g ∈ cell ϖ b := right_translate_mem_cell

end GlobalTheory.IwaCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivativesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ 𝒮 : Set (GA D V → ℂ), (∀ φ ∈ 𝒮, Continuous φ) → (∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt V τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (φ' g) 0) → ∀ φ ∈ 𝒮, φ ∈ SmFun θ V := by
  first | exact @GlobalTheory.Mem.DerClosed.mem_smFun_of_closed | exact GlobalTheory.Mem.DerClosed.mem_smFun_of_closed | (intros; apply GlobalTheory.Mem.DerClosed.mem_smFun_of_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibilityStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_function_field_compatibility : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y), haveI := M.ar.isIntegral; ∃ ρ : M.X.functionField ≃+* Y.Fn, (∀ (U : M.X.Opens) (hU : genericPoint M.X ∈ U) (hU' : genericPoint Y.X ∈ M.j ⁻¹ᵁ U) (s : Γ(M.X, U)), ρ (fnOf U hU s) = fnOf (M.j ⁻¹ᵁ U) hU' (M.j.app U s)) ∧ M.j (genericPoint Y.X) = genericPoint M.X ∧ (∀ (x : Y.X) (f : M.X.functionField), RegAt (M.j x) f ↔ RegAt x (ρ f)) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Y.X) (f : M.X.functionField), valAt (y ≫ M.j) f = valAt y (ρ f)) ∧ ∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))), y'.1 = y.1 ≫ M.j → ∀ f : M.X.functionField, ratVal f y' = ratVal (ρ f) y := by
  first | exact @GlobalTheory.TrueGeo.ModelFn.main | exact GlobalTheory.TrueGeo.ModelFn.main | (intros; apply GlobalTheory.TrueGeo.ModelFn.main <;> assumption)
end

