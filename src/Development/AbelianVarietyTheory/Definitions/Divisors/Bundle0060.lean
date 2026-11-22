import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0036
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Formalism.SharpRestriction.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

protected abbrev zsc {D : D7} {O : Obj D} (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  GlobalTheory.Fc.zsc P Del h0 c

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Part (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : Formalism.L2.RecT O.ex
  S : Formalism.L2.SG.SpectralTiesReal.STiesR R
  P : RowSideFamily O.ex
  pin : RowSideDetermined R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : RealTB R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : RealRec B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : RealPins B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : RealRecPins pins Rr

def PFire : BdP Part := fun _ _ _ b =>
  b.B.Q.Rl.toRealDat.ExAt ∧ JEvBar b.B.T b.B.Q.Rl.toRealDat b.B.κ ∧ GeoAct b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ ∧
    EvInj b.B.T b.B.Q.Rl.toRealDat b.B.v₀

def PRB : BdP Part := fun _ _ _ b => RowsB b.B

def PThR : BdP Part := fun _ _ _ b =>
  RecTie.ThetaFireRow (RecTie.toLiftReal b.B.Q.Rl.toRealDat b.B.Q.F.lv2 b.Rr.tupT b.Rr.hm b.Rr.hTop b.Rr.hinj) b.Rr.IL

def PFrames : BdP Part := fun _ _ _ b => RealT.FramesEx b.B.Q

def PSeeEx : BdP Part := fun _ _ _ b => SeeEx b.B.Q

def PPA : BdP Part := fun _ _ _ b => PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3

def PDiv : BdP Part := fun D O _ b =>
  DivRows3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.Zs b.P.S0 b.P.S1 O.ex.p0 b.P.C b.P.NuC b.P.I

def BaseRankDimension : BdP Part := fun D _ _ b =>
  D.what₂.D0 = (b.P.A3.A.fam.R b.P.A3.A.fam.μ0).dZ (b.P.A3.A.fam.lvl b.P.P0 b.P.ψ0) (b.P.Zs.Z b.P.A3.A.fam.μ0)

def PNmj : BdP Part := fun _ O _ b => NX.NMjT b.B.Q b.B.Q.cG b.B.Q.Sx b.B.Q.nexp O.ex.nch

def PIota : BdP Part := fun _ _ _ b => ∀ x : b.S.X.B.I.E, HEq (b.S.X.ιE x) x

def L3 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)

def ON (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)

def L6 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)

def FUN (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)

def Small (C CH : ℝ) : BdP Part := fun _ _ _ b =>
  (∀ w, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F C CH) w → w ∈ b.B.Q.Rl.twPl) ∧
    (b.B.Q.Rl.toCx3 b.B.Q.F).SEEIso b.B.Q.sEE ∧ PassIn3 b.B.Q.Rl b.B.Q.F C CH

variable {Bd : BdT}

def Ev {𝒜 : FamClass} (σ : RawSel Bd 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (q : BdP Bd) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, q _ _ _ (σ Fm hc x hx i)

def EvW (q : BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : W3 𝒜 Fm, Ev σ Fm (w3_a hc) q

def EvWC (prem : ∀ {eps : ℝ}, FamP eps → Prop) (q : ℝ → ℝ → BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm CH => ∀ hc : W3 𝒜 Fm, prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ev σ Fm (w3_a hc) (q C CH)

theorem ev_of_atAll {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {q : BdP Bd} (h : AtAll q 𝒜 σ) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) :
    Ev σ Fm hc q := ⟨0, fun x hx _ i => h Fm hc x hx i⟩

example {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) (Rr : RealRec b.B.Q)
    (psi : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG) (pins : RealPins b.B.Q)
    (muDef : ∀ C CH : ℝ, (b.B.Q.Rl.toCx3 b.B.Q.F).MuDef b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F C CH) b.B.Q.Rl.mu)
    (recPins : RealRecPins pins Rr) : ∃ p : Part D O c, HEq p.B b.B ∧ (PRB D O c p ↔ RowsB b.B) :=
  ⟨⟨b.R, b.S, b.P, b.pin, b.DH, b.C.c.face, b.C.Sp, b.C.ok1, b.B, Rr, psi, pins, muDef, recPins⟩, HEq.rfl, Iff.rfl⟩

example {D : D7} {O : Obj D} (P : RowSideFamily O.ex) (Del h0 : ℕ) (c c' : ℝ) (Zs : DefSub P.A3.fam3.amb3) :
    (zsc P Del h0 c Zs).F0 = (zsc P Del h0 c' Zs).F0 ∧ (zsc P Del h0 c Zs).l6u = 0 := ⟨rfl, rfl⟩

end GlobalTheory.Fc.Ind

open GlobalTheory.Fc GlobalTheory.Fc.Ind in

example {D : D7} {O : Obj D} (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) : zsc P Del h0 c = Ind.zsc P Del h0 c := rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

def IsCurve (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] : Prop :=
  SmoothOfRelativeDimension 1 (strHom k C) ∧ IsProjOver (strHom k C) ∧ GeometricallyConnected (strHom k C)

def SemiNeg (k : Type) [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (F : C.Modules) : Prop :=
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ i : W ⟶ F, Mono i → interNum k (structureModule C) ![det W r] ≤ 0

def IsGen {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) : Prop := IsDominant x ∧ IsPreimmersion x

theorem isGen_fromSpecStalk (C : Scheme.{0}) [IsIntegral C] :
    IsGen (K := C.functionField) (C.fromSpecStalk (genericPoint C)) :=
  ⟨show IsDominant (C.fromSpecStalk (genericPoint C)) from ⟨by
      refine Dense.mono (s₁ := {genericPoint C}) ?_ (dense_iff_closure_eq.2 (genericPoint_spec C).def)
      rintro _ rfl
      exact ⟨_, Scheme.fromSpecStalk_closedPoint⟩⟩,
    inferInstanceAs (IsPreimmersion (C.fromSpecStalk (genericPoint C)))⟩

structure IsNeron {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) (N : Over C) : Prop where
  smooth : Smooth N.hom
  separated : IsSeparated N.hom
  quasiCompact : QuasiCompact N.hom
  ext : ∀ Y : Over C, Smooth Y.hom → Function.Bijective fun f : Y ⟶ N ↦ (Over.pullback x).map f

end GlobalTheory.NeronCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
section
noncomputable section

open Matrix GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.DetInv

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O C] [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h : ℕ}
  {Γ : Type} [CommRing Γ] [Algebra ℤ_[p] Γ]

structure IsTie (P : Point p v O Λ) (D : Datum ε h Γ) (j : Λ →+* Γ)
    (φ : P.V ≃ₗ[C] (Fin h → C)) : Prop where
  lat : ∀ x, x ∈ P.latT ↔ ∀ i, φ x i ∈ (algebraMap O C).range
  act : ∀ a x, φ (P.actV a x) = (actT D (j a)).map (algebraMap O C) *ᵥ φ x
  lie : ∀ x, x ∈ P.latLie ↔ φ x ∈ D.Lie.map (incl C h)
  lieInj : Function.Injective P.bLie
  ker : ∀ x, x ∈ P.W ↔ alC C D (φ x) = 0
  fil : ∀ x, (∀ i, alC C D (φ x) i ∈ (algebraMap O C).range) ↔
    ∀ y ∈ P.latLie, P.pairV y x ∈ (algebraMap O C).range

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MoveArgsOneTranspose
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.LocTest

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem flipOrder_nodup (m : ℕ) : (flipOrder m).Nodup ∧ ∀ i j, (i, j) ∈ flipOrder m ↔ i < m ∧ j < m :=
  ⟨List.Nodup.product (List.nodup_range (n := m)) (List.nodup_range (n := m)), fun i j => by simp [flipOrder]⟩

example : Module.Free (AF D.host.F) (AE D) ∧ Module.Finite (AF D.host.F) (AE D) := ⟨inferInstance, inferInstance⟩

theorem moveArgs_one_transpose {k : Type*} [Field k] (Γ : Grid k) (g : Γ.VertexGroup) (x : Γ.Args) (b : Edge) :
    (Γ.moveArgs .one g x b)ᵀ = ((g b.src)⁻¹).val * (x b)ᵀ * (g b.tgt).val := by
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, transpose_mul, transpose_transpose, Matrix.mul_assoc]

theorem stepFn_twist (t : T) (w : Pl D.host.E) (h1 : w ∉ L.Pg) (h2 : w ∈ L.Q t) (j : ℕ)
    {g : GL (Fin D.R.r) (Kw w)} (hg : g ∈ KO (Kw w) _) :
    stepFn L t w j (fromBlocks g.val 0 0 0) = ((L.xiH t).loc w (GeneralLinearGroup.det g) : ℂˣ) := by
  rw [stepFn, if_neg h1, if_pos h2, parPhi_fromBlocks _ hg rfl maxM_zero intM_zero intM_zero]
  simp

theorem hasTypes_twist (G : GridData L sc) (t : T) (w : Pl D.host.E) (h1 : w ∉ L.Pg) (h2 : w ∈ L.Q t) (j : ℕ)
    (hξ : IsTame ((L.xiH t).loc w)⁻¹) (hμ : IsUnram ((muBase L (j + 1)).loc w)⁻¹) :
    HasTypes ((locGrid G t w).mu (j + 1))⁻¹ (parahoric _ _ _ hξ).toLevel (parahoric _ _ _ hξ).toLevel (stepFn L t w j) := by
  have e : ((locGrid G t w).mu (j + 1))⁻¹ = ((muBase L (j + 1)).loc w)⁻¹ * ((L.xiH t).loc w)⁻¹ := by
    rw [← mul_inv]; rfl
  rw [e, stepFn, if_neg h1, if_pos h2]
  exact hasTypes_parPhi hξ hμ

theorem stepGroup_twist (t : T) (w : Pl D.host.E) (h1 : w ∉ L.Pg) (h2 : w ∈ L.Q t) (j : ℕ)
    (hξ : IsTame ((L.xiH t).loc w)⁻¹) : stepGroup L t w j = (parahoric _ _ _ hξ).J := by
  rw [stepGroup, if_neg h1, if_pos h2]; rfl

theorem intM_of_stepFn (t : T) (w : Pl D.host.E) (j : ℕ) {x} (h : stepFn L t w j x ≠ 0) : IntM x := by
  unfold stepFn at h
  split_ifs at h
  · intro i l
    simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h ((ixSucc _ _ j).symm i) l
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff _).1 h
    rintro (i | i) (l | l)
    · have := intM_of_mem_KO hg i l
      rwa [e] at this
    · exact h12 i l
    · exact (h21 i l).le
    · exact h22 i l
  · by_contra hx
    exact h (Set.indicator_of_notMem (s := {x | IntM x}) hx _)

theorem givenStage_not_const {G : GridData L sc} (t : T) (w : Pl D.host.E) (B : Frames G) (Φ : G.Datum) :
    (∃ x, (givenStage t w B Φ).tensor x = 1) ∧ ∃ x, (givenStage t w B Φ).tensor x = 0 := by
  refine ⟨exists_givenStage_eq_one t w B Φ, fun _ => Matrix.of fun _ _ => ((unifAt w)⁻¹ : (Kw w)ˣ), ?_⟩
  have hm := D.R.two_le_m
  refine List.prod_eq_zero (List.mem_map.2 ⟨.theta 0 0, by simp [givenPath]; omega, ?_⟩)
  by_contra h
  have hr : 0 < D.R.r := (odd_r D).pos
  have h1 := intM_of_stepFn t w 0 h (.inl ⟨0, hr⟩) (.inl ⟨0, hr⟩)
  have h2 : valuation (Kw w) ((unifAt w : (Kw w)ˣ) : Kw w) < 1 := (isUnif_unifAt w) ▸ uniformizer_lt_one
  have h3 : valuation (Kw w) (((unifAt w)⁻¹ : (Kw w)ˣ) : Kw w) ≤ 1 := h1
  have h4 := mul_lt_one_of_lt_of_le h2 h3
  rw [← map_mul, Units.mul_inv, map_one] at h4
  exact lt_irrefl _ h4

theorem flips_eq_zero {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (l : List (ℕ × ℕ)) (S : Γ.PiLocalization₂)
    (i j : ℕ) (x : Γ.Args) (hx : x (.theta (i + 1) j) ∉ matLat _ (stdLat k _)) :
    (S.flips .one ψ ϖ e (l ++ [(i, j)])).tensor x = 0 := by
  rw [Grid.PiLocalization₂.flips, List.foldl_append]
  change invFourierSum _ _ _ _ _ _ = 0
  rw [invFourierSum_apply, if_neg]
  intro h
  refine hx (mem_matLat_stdLat.2 fun a b => ?_)
  exact h b (.inr a) (by simp [Assignment.block])

theorem Tflip_eq_zero {G : GridData L sc} (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E) {n : ℕ}
    (hn : D.R.m = n + 1) (x : (locGrid G t w).Args) (hx : x (.theta (n + 1) n) ∉ matLat _ (stdLat (Kw w) _)) :
    Tflip W B t Φ w x = 0 := by
  have e : ∃ l, flipOrder D.R.m = l ++ [(n, n)] := by
    rw [hn, flipOrder, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append, ← List.append_assoc]
    exact ⟨_, rfl⟩
  obtain ⟨l, e⟩ := e
  rw [Tflip, flipStage, e]
  exact flips_eq_zero _ _ _ _ _ _ _ _ hx

theorem edgeFactor_theta {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : Grid k) (hη : IsUnram Γ.eta) (g : Γ.VertexGroup) (hg : ∀ X, g X ∈ KO k _) (i j : ℕ)
    (Φ : Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k → ℂ) (x : Γ.Args) :
    Γ.edgeFactor .one g (.theta i j) * Φ (Γ.moveArgs .one g x (.theta i j))ᵀ =
      om (Γ.mu (j + 1))⁻¹ (g (i, j)) (g (i, j + 1)) Φ (x (.theta i j))ᵀ := by
  have h1 : ∀ X, Γ.eta (gdet (g X)) = 1 := fun X => hη _ (valuation_gdet_of_mem_KO (hg X))
  rw [om_of_mem_KO _ (hg _) (hg _), moveArgs_one_transpose]
  simp only [Grid.edgeFactor, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hg _)))]
  have h2 : ∀ X, Γ.kappa (.theta i j) X (gdet (g X)) = Γ.mu (j + 1) (gdet (g X)) := fun X => by
    simp [Grid.kappa, Grid.blockChar, h1]
  rw [h2, h2, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv, mul_one, mul_one, mul_comm (Γ.mu _ _ : ℂ)]

end GlobalTheory.FunObj.LocTest

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OfDat
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {Tw : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}

theorem TiesA.of_dat (z : Dat X I hX Tw Wt)
    (ok : (famR X I hX (usedOf I Tw Wt) z.Xg z.tr).fam3.Ok3 1) (hex : z.R.toRealDat.ExAt)
    (host : Formalism.IndefR.Links.HostHyp X.toD7) (par : ∃ L : SizeData₂ X.toD7, Nonempty (ParameterChoice' X.toD7 L))
    (ty : GlobalTheory.Mem.Top.TypesTrue X.toD7.ntypes z.R.C.P z.R.C.W) (ser : SerClause X.toD7)
    (w1 : ∀ w, (z.R.toCx3 z.F).W1 z.F.cr (z.R.num z.F 0 0) w → w ∈ z.R.twPl)
    (nV : 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) : TiesA z.R z.F :=
  ⟨ok, z.pins.char, hex, host, par, X.B.ccK_top, z.pins.keep.guard,
    GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue z.pins.char.base.lev ty, ser,
    GlobalTheory.Hk3.inertJunk_colIn3 _ _ _ hX _ _ _ _ _ _, z.pins.trSem, z.pins.keep.std, z.pins.phs, w1, nV⟩

theorem TiesG.of_dat (z : Dat X I hX Tw Wt) (hU : z.R.toRealDat.LUnif) (hI : IoExt z.R.toRealDat)
    (hM : ∀ i, OneMapRowR z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) i)
    (hC : GlobalTheory.TwistField.CoverField z.core z.R.toRealDat) : TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have e : (fun i => cj (twAt X.toD7.what₂.embLL (famR X I hX (usedOf I Tw Wt) z.Xg z.tr).A.v0) (z.R.phs i)) = fun _ => (1 : ℂ) := by
    funext i
    rw [z.pins.phs i]
    exact map_one _
  refine ⟨⟨z.geo.fw, z.geo.bar⟩, z.geo.pins, ?_, hU, hI, ?_, hC⟩
  · rw [e]; exact z.geo.phase
  · rw [e]; exact hM

end GlobalTheory.PrimIn

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Params
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}

structure TiesB {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ok : A3.fam3.Ok3 1
  char : R.WeakCharacterisation F
  ex : R.toRealDat.ExAt
  host : Formalism.IndefR.Links.HostHyp D
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  ccK : D.host.ccK = ⊤
  guard : QGuard R.toRealDat
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat
  ser : SerClause D
  junk : GlobalTheory.Hk3.InertJunk A3
  trSem : (∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep
  std : IsStdChar D R.ψ (-1)
  phs : ∀ i, R.phs i = 1
  nV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

theorem TiesA.toB {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (h : TiesA R F) : TiesB R F :=
  ⟨h.ok, h.char, h.ex, h.host, h.params, h.ccK, h.guard, h.types, h.ser, h.junk, h.trSem, h.std, h.phs, h.nV⟩

end GlobalTheory.PrimIn

end
end

