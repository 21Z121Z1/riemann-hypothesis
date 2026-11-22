import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0615
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0832
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0175
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GalRead

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerRatAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_rationality_of_reciprocity_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.kerRatAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.kerRatAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.kerRatAt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_relaxed_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∃ U0 : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), U0 ≤ GfC _ ∧ IsCompact (U0 : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → (∀ g ∈ U0, GlobalTheory.FinPl.Moves _ g (a.g.x j).L (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)) ∧ (∀ κ, GlobalTheory.FinPl.InK _ (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) κ → κ ∈ U0) ∧ ∀ α, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ U0 ∧ ∀ i, c i * _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))) := by
  first | exact @_root_.GlobalTheory.PenLev.levels_alt | exact _root_.GlobalTheory.PenLev.levels_alt | (intros; apply _root_.GlobalTheory.PenLev.levels_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTiesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sum_divisor_all_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  first | exact @_root_.GlobalTheory.GeoTies.linked_ties_alt | exact _root_.GlobalTheory.GeoTies.linked_ties_alt | (intros; apply _root_.GlobalTheory.GeoTies.linked_ties_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.at_statement_of_low_weight_twAdm : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.rowAt_of_alt | exact _root_.GlobalTheory.BigOn.Exp.rowAt_of_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.rowAt_of_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeIdentityOfIsTriple
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Triple
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)
variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}
section With
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : Zbar (X.l i) →+* FbAt D w}
theorem IsGaloisTripleWithReduction.unrRho {b : Bool} {ρ : Reading X i b} (ha : IsGlobalArtin art)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : UnrRho i s := by
  intro v hl hg A hA g hgI
  obtain ⟨n, hn⟩ := h.shift
  have e := h.rho g
  rw [_root_.GlobalTheory.Triple.unramified_of_isGaloisRepOfN_of_unr h.gal hl (h.param.unr v hg) hA hgI,
    (hn.unr_iff ha (Or.inl hl) hA).2 (shiftChar_unr C v) g hgI, Units.val_one, map_one, one_smul, Units.val_one] at e
  refine Units.ext (Matrix.map_injective (GlobalTheory.GalChar.toQ_injective ρ.κ) ?_)
  simpa using e
theorem IsGaloisTripleWithReduction.charpolyRev_matW {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) {B : ValuationSubring D.nd.Om}
    (hB : IsPlaceOver (F := D.host.E) B P) {g : GalE D} (hF : IsFrob (F := D.host.E) B (normV P) g⁻¹) :
    (matW s g).charpolyRev.map ρ.toC = ((satake (muBase C (X.l i) (jIdx s)) π P).map fun α =>
      1 - Polynomial.C (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2) * α) * Polynomial.X).prod := by
  have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
  have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
  obtain ⟨n, hn⟩ := hC.chiS
  have hu := (hn.unr_iff ha (Or.inl hl) hB).1 (X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) B hB)
  have e1 := h.charpoly_frob ha hl hg hB hF
  have e2 : ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) =
      (((blockChar C (X.l i) (jIdx s)).val P : ℂˣ) : ℂ) * ((normV P : ℕ) : ℂ) ^ D.R.t := by
    rw [twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_pow_eq_pow_val,
      cyclotomicEps_frobenius_eq_norm hl hB hF, map_mul, map_pow, map_natCast, map_units_inv, ρ.toC_apply,
      hn.frob ha (Or.inl hl) hu hB hF, inv_inv, mul_comm]
  rw [← Matrix.charpoly_map, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e1
  have e3 := charpoly_smul_of_prod _ _ (ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i)) e1
  have e4 : (matW s g⁻¹).map ρ.toC = ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) •
      ((X.rhoS i s g⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map ρ.toC := by
    ext x y
    simp [matW]
  rw [← e4, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e3
  have e5 : (matW s g).map ρ.toC * (matW s g⁻¹).map ρ.toC = 1 := by
    rw [← Matrix.map_mul, matW_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [charpolyRev_map, charpolyRev_of_inv e5 e3, satake, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [← geometric_eigenvalue, e2, ← mul_assoc]
theorem IsGaloisTripleWithReduction.hkFrob {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : HkFrob i s := by
  intro P hS hP g hF k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hP hS
  have e := congrArg (fun p => coeff p k) (h.charpolyRev_matW ha hC hS (D.nd.plOm.2 P) hF)
  simp only [coeff_map, GlobalTheory.coeff_prod_one_sub_C_mul_X] at e
  have e2 : ((normV P : ℕ) : ℂ) ^ (k * (k - 1) / 2) * heckeVal (muBase C (X.l i) (jIdx s)) π k P =
      (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) ^ k * (satake (muBase C (X.l i) (jIdx s)) π P).esymm k :=
    (pow_mul_heckeVal _ π P hk).trans
      (Multiset.pow_smul_esymm (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) k (satake (muBase C (X.l i) (jIdx s)) π P)).symm
  have e3 : (-1) ^ k * ((normV P : ℕ) : X.O0 i) ^ (k * (k - 1) / 2) * x = (matW s g).charpolyRev.coeff k := by
    apply ρ.toC_injective
    rw [e, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, h2, mul_assoc, e2, mul_assoc]
  rw [← matW_eq, ← e3, ← h1, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast]
end With
variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}
theorem IsGaloisTripleOfExpansion.unrRho (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : UnrRho i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, _, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.unrRho h.artin
theorem IsGaloisTripleOfExpansion.hkFrob (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : HkFrob i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, h1, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.hkFrob h.artin h1
theorem IsGaloisTripleOfExpansion.adm8 (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : adm8 X Y := by
  intro i hi s _
  have hu := h.unrRho hi s
  refine ⟨twistW s, ?_, fun P hS _ A hA g hI => ?_, fun v hv A hA => ?_, fun P hS hP g hF => ?_⟩
  · obtain ⟨ρ⟩ := Reading.nonempty i true
    exact Units.continuous_val.comp
      (((GlobalTheory.GalChar.continuous_units _ (GlobalTheory.GalChar.continuous_cyc (X.twistBaseCoefficientRing_isAdic i) ρ.κ_alg)).pow D.R.t).mul
        (GlobalTheory.GalChar.continuous_units _ (X.twistCharacterFamily_continuous i _ _)).inv)
  · have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
    have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
    refine (matW_of_mem_Ine hu hl hg hA hI).trans ?_
    rw [chiS, X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) A hA g hI, inv_one, Units.val_one, one_smul]
  · obtain ⟨hl, hg⟩ := notMem_of_mem_pD hv
    cases hb : X.side i s
    · refine Or.inl fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_neg Bool.false_ne_true, inv_inv]
    · refine Or.inr fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_pos rfl]
  · change _ = algebraMap (X.O0 i) (X.O i) (1 - matW s g).det
    rw [← sum_coeff_charpolyRev, map_sum, matW_eq]
    exact Finset.sum_congr rfl fun k hk => h.hkFrob hi s P hS hP g hF k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
theorem adm8_allGood_sig_of_isTriple (D : D7) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) :
    Formalism.MainNotions.BlochKatoReduction.Gen.adm8 D.ntw D.nexp ∧ GlobalTheory.TwSys.AllGood D.nexp ∧ D.nexp.sig_all :=
  ⟨_root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.adm8 h, _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.allGood h, _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.sig_all h⟩
end GlobalTheory.Triple
end
end
end

