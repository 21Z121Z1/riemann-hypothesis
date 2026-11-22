import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0614
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0146
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0172
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0830
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0154
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0116
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0131
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0097
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0173
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0098
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0169
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0079
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0157
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0103

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Adm2OfIsTriple
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleAdm
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual
section Algebra
variable {g : ℕ} [Fact g.Prime]
end Algebra
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host
variable {D : D7}
section Row
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}
end Row
section Comparison₂
variable {Y : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : Y.Tw} {b : Bool}
variable {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}
theorem exists_kappa_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) {s : Y.Sig i} {ρ : Reading Y i (Y.side i s)}
    (hχ : IsChars C art ρ) {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (Y.l i))}
    {ν : GalE D →* (Y.O0 i)ˣ} {w : D.what₂.places.Pl} {red : Zbar (Y.l i) →+* FbAt D w}
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : ∃ κ, IsRowOfTriple Y i s σ w κ := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hl := h.induces.resChar
  obtain ⟨κ, hκ⟩ := exists_residue_lift ρ (red.comp (toZ ρ)) (by rw [← hl]; exact CharP.cast_eq_zero _ _)
  refine ⟨κ, h.good, h.occurs, hl, fun x => ?_,
    ⟨(Units.map (red.comp (toZ ρ)).toMonoidHom).comp ν, fun v hv A hA t ht => ?_, fun g => ?_⟩, fun k hk v => ?_⟩
  · obtain ⟨-, -, hint, -⟩ := GlobalTheory.CoefEmbed.embedding_closed_integral _ _ (Y.twistBaseCoefficientRing_isAdic i) ρ.κ ρ.κ_alg
    have e : ∀ y : ↥D.LL0, ρ.ι.symm (D.what₂.embLL (y : D.what₂.LL)) = ρ.κ (GlobalTheory.Triple.embSide Y i (Y.side i s) y) :=
      fun y => by rw [RingEquiv.symm_apply_eq, ρ.read]; rfl
    have h1 : 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔
        ‖ρ.κ (GlobalTheory.Triple.embSide Y i (Y.side i s) (x : ↥D.LL0))‖ < 1 := by
      rw [← e]
      generalize ((x : ↥D.LL0) : D.what₂.LL) = y
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      have h2 := h.induces y⁻¹
      have h3 : 0 < ‖ρ.ι.symm (D.what₂.embLL y)‖ := by simpa using hy
      rw [map_inv₀ D.what₂.embLL, map_inv₀ ρ.ι.symm, norm_inv, inv_le_one₀ h3] at h2
      rw [← not_le, ← not_le, ← h2, not_iff_not, AddValuation.map_inv]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 ((D.what₂.places.val w).ne_top_iff.2 hy)
      rw [← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_zero, WithTop.coe_le_coe,
        WithTop.coe_le_coe, neg_nonneg]
    rw [h1]
    refine ⟨?_, fun h2 => ?_⟩
    · rintro ⟨y, hy, e1⟩
      rw [GlobalTheory.Triple.embSide, ← e1]
      exact (mem_maximalIdeal_iff ρ y).1 hy
    · obtain ⟨y, hy⟩ := hint _ h2.le
      exact ⟨y, (mem_maximalIdeal_iff ρ y).2 (by rw [← hy] at h2; exact h2), hy⟩
  · obtain ⟨n, hn⟩ := h.shift
    rw [MonoidHom.comp_apply, (hn.unr_iff ha (Or.inl hv) hA).2 (GlobalTheory.Triple.shiftChar_unr C v) t ht, map_one]
  · obtain ⟨p, h1, h2⟩ := h.residual.charpoly g
    let M : Matrix (Fin D.R.r) (Fin D.R.r) (Y.O0 i) := (((ν g)⁻¹ : (Y.O0 i)ˣ) : Y.O0 i) •
      ((Y.rhoS i s g : GL (Fin D.R.r) (Y.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (Y.O0 i))
    have e1 : (M.map (toZ ρ)).map (Zbar (Y.l i)).subtype = (r g : GL (Fin D.R.r) (Qbar (Y.l i))) := by
      ext x y
      have := congrFun (congrFun (h.rho g) x) y
      change toQ ρ.κ (_ * _) = _
      rw [map_mul]
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [this, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    have e2 : p = (M.map (toZ ρ)).charpoly :=
      Polynomial.map_injective (Zbar (Y.l i)).subtype Subtype.val_injective (by rw [h1, ← Matrix.charpoly_map, e1])
    rw [e2, ← Matrix.charpoly_map] at h2
    rw [← charpoly_smul_congr _ h2]
    congr 1
    ext x y
    change κ (IsLocalRing.residue _ _) = red (toZ ρ (ν g : (Y.O0 i)ˣ)) * red (toZ ρ (_ * _))
    rw [hκ, ← map_mul, ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rfl
  · obtain ⟨u, hu, e⟩ := hχ.tame (jIdx s) k hk.symm v
    refine ⟨u, hu, (hκ _).trans (h.residual.teich k hk.symm v _ (toFb_ne_zero k u) _ ?_)⟩
    rw [← e, GlobalTheory.Triple.jIdx_add_one, Reading.toC_apply, RingEquiv.symm_apply_apply]
    rfl
variable {Z : NExp D.R D.host D.what₂ D.LL0 D.nd Y}
theorem blockCharConj_of_isTripleOf (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Z) : BlockCharConj Y := by
  obtain ⟨C, art, h⟩ := h
  intro i hi j b h1 h2 k hk v hv A hA t ht t' ht'
  obtain ⟨ρ, hχ, -⟩ := h.evidence i hi b
  obtain ⟨j, rfl⟩ : ∃ j' : Fin D.R.m, j = j'.1 + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨n, hn⟩ := hχ.chi j
  obtain ⟨n0, h0⟩ := exists_isAlgPos_mu0 (hframe C) GlobalTheory.Triple.eExp_int j
  obtain ⟨r, hr, hL⟩ := h.artin.exists_isLAdicOf ρ.ι (isAlgPos_mul h0 (del_alg (hframe C) (Y.l i)))
  have hanti : AntiHom Y.cc r := antiHom_of_isLAdicOf h.artin hr hL
    (((hframe C).isMu0 j).triv.mul (inertialOrderFifteenChar_auxiliaryPrime_spec (hframe C) (l := Y.l i)).2.2.2.2.triv)
  have key : ∀ v, v ∉ placesOver D.host.E (Y.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ t ∈ Ine (F := D.host.E) A, inQ ρ.κ (Y.chi1 i (j.1 + 1) b) t = r t := fun v hv A hA t ht => by
    obtain ⟨x, hx, e⟩ := exists_unit h.artin hA ht
    have e1 := hn.loc (Or.inl hv) e
    rw [GlobalTheory.Triple.blockChar, block_loc (C.isEta.unr v) hx] at e1
    apply Units.ext
    rw [hL.loc_away (Or.inl hv) x t e, inQ_val, RingEquiv.eq_symm_apply]
    exact e1
  have hvl : v ∉ placesOver D.host.E (Y.l i) := notMem_of_ne (D.host.g_prime k) (Y.lPrime i).out hk hv
  obtain ⟨bar, -, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  obtain rfl : t' = cConj Y t := AlgEquiv.ext ht'
  rw [← map_inv]
  refine inQ_inj ρ.κ ?_
  rw [map_inv, key v hvl A hA t ht, key (bar v) (fun hm => hvl (mem_placesOver_conj (TwistDet.isConjPl_symm (hbar v).1) hm)) _
    (isPlaceOver_moveVal_cc Y (hbar v).1 hA) _ (cConj_mem_ine Y ht), hanti t _ ht']
theorem gen_adm2_of_isTripleOf (hT : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Z) (hW : WildOne D) : BlochKatoReduction.Gen.adm2 Y := by
  intro i hi s
  have hχ := _root_.GlobalTheory.TripleAdm.blockCharConj_of_isTripleOf hT
  obtain ⟨C, art, h⟩ := hT
  obtain ⟨ρ, h1, σ, π, r, ν, w, red, h2⟩ := h.triple hi s
  obtain ⟨κ, h3⟩ := _root_.GlobalTheory.TripleAdm.exists_kappa_of_isTripleWith h.artin h1 h2
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hl := h2.induces.resChar
  obtain ⟨hirr, hrow⟩ := _root_.GlobalTheory.TripleAdm.irredOn_rbar_and_inertia_of_residual Y hW h2.good h2.param hl h2.gal h2.residual
  refine admissible_at_of_irreducible_tame h3 hirr fun k hk v hv A hA => ?_
  refine tameOff_all Y (fun e => hk (e.symm.trans hl)) (D.ntypes.rbar_open σ w) (fun v => (hrow k hk.symm v).1)
    (fun v t ht => ?_) (fun v => ⟨(hrow k hk.symm v).2.1, ?_⟩) hv hA
  · have := hχ i hi _ (Y.side i s) (Y.jS_range i s).1 (Y.jS_range i s).2 k hk _ (D.naut.plGw_over k v) _
      (D.nd.plOm.2 _) t ht _ (cConj_apply Y t)
    rw [← map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, map_inv]
    exact congrArg _ this
  · obtain ⟨u, hu, e⟩ := h3.2.2.2.2.2 k hk v
    exact ⟨_, D.ntypes.tg_mem k v, fun h0 => (hrow k hk.symm v).2.2 _ u hu (e ▸ h0)⟩
end Comparison₂
theorem adm2_of_isTriple_wildOne (D : D7) (hT : _root_.GlobalTheory.Triple.IsGaloisTriple D) (hW : WildOne D) : BlochKatoReduction.adm2 D := _root_.GlobalTheory.TripleAdm.gen_adm2_of_isTripleOf hT hW
end GlobalTheory.TripleAdm
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsTripleWithcharpolyFrob
section
theorem GlobalTheory.Triple.IsGaloisTripleWithReduction.charpoly_frob : type_of% (@GlobalTheory.Triple.IsGaloisTripleWithReduction.charpoly_frob_of_isTriple) := @GlobalTheory.Triple.IsGaloisTripleWithReduction.charpoly_frob_of_isTriple
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundlePackEqAdelicDataStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_lines_of_cusp_rapid_decay : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) := by
  first | exact @_root_.GlobalTheory.Fam.PtRowsAt.good_linked_ptR_of_cuspRapidDecay | exact _root_.GlobalTheory.Fam.PtRowsAt.good_linked_ptR_of_cuspRapidDecay | (intros; apply _root_.GlobalTheory.Fam.PtRowsAt.good_linked_ptR_of_cuspRapidDecay <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChoiceSide
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.choiceSide_alt {low Pq S hk eig θ} {Bs : SideB D cf A.row low Pq S hk eig θ} (x : ChoiceSide D cf M Bs.exp C tp) : ChoiceSide m.D (m.cf cf) (m.mt M) (m.sideB_alt Bs).exp (m.ch C) (m.tp tp) := @_root_.GlobalTheory.HeightCounting.ChoiceSide.mk (_) (_) (_) (_) (_) (_)
    (nct := @_root_.Formalism.BasicNotions.NChTie.mk (_) (_)
      (twOf_eq := (by with_unfolding_all exact (x.nct.twOf_eq :)))
      (twSide_eq := (by with_unfolding_all exact (x.nct.twSide_eq :)))
      (Q_eq := (by with_unfolding_all exact (x.nct.Q_eq :)))
      (psi_eq := (by with_unfolding_all exact (x.nct.psi_eq :)))
      (embedding_baseField_condition := (by with_unfolding_all exact (x.nct.embedding_baseField_condition :))))
    (choice := @_root_.GlobalTheory.HeightCounting.ChoiceC.mk (_) (_)
      (twI_conj := (by with_unfolding_all exact (x.choice.twI_conj :)))
      (sd_place := (by with_unfolding_all exact (x.choice.sd_place :)))
      (emb_side := (by with_unfolding_all exact (x.choice.emb_side :)))
      (sd_conj := (by with_unfolding_all exact (x.choice.sd_conj :)))
      (one := (by with_unfolding_all exact (x.choice.one :)))
      (conj := (by with_unfolding_all exact (x.choice.conj :))))
    (off := (by with_unfolding_all exact (x.off :)))
    (adm := (by with_unfolding_all exact (x.adm :)))
    (psi := (by with_unfolding_all exact (x.psi :)))
    (eMt_level := (by with_unfolding_all exact (x.eMt_level :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DatExistsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∃ s ζ ρ, J.Dat C s ζ ρ := by
  first | exact @_root_.GlobalTheory.Fam.QuadraticExtensionData.dat_exists | exact _root_.GlobalTheory.Fam.QuadraticExtensionData.dat_exists | (intros; apply _root_.GlobalTheory.Fam.QuadraticExtensionData.dat_exists <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DegLieCoreStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degLie_eq_neg_flatDegVal_at_last_index : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  first | exact @_root_.GlobalTheory.DefCoreLie.degLie_core_alt | exact _root_.GlobalTheory.DefCoreLie.degLie_core_alt | (intros; apply _root_.GlobalTheory.DefCoreLie.degLie_core_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAd
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenLocAt
theorem exists_ad_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ c => Nonempty (MtAd t.r.Y c.a.all.gal.mt) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE _ _ => hE.elim fun e => ⟨_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.ad e⟩
set_option maxHeartbeats 2000000 in
theorem cenLoc_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenRat_at_members hL) (_root_.GlobalTheory.T.actRead_at_member_of_recT hL)) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members hL) (_root_.GlobalTheory.CenLocAt.exists_ad_alt hL)))
    fun _ _ _ _ _ _ _ _ t _ _ _ h => h.2.2.elim fun ad => cenLoc_of t.r.Y t.r.z.cG _ ad h.1.1 h.1.2 (h.2.1 ad)
end GlobalTheory.CenLocAt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleOfSideBStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_export_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → _root_.GlobalTheory.EigTie.ResTiedAlt D Rw → _root_.GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisRepsAlt D → D.nexp.sig_all → _root_.GlobalTheory.Triple.IsGaloisTriple D := by
  first | exact @_root_.GlobalTheory.TripInhab.isTriple_of_sideB_alt | exact _root_.GlobalTheory.TripInhab.isTriple_of_sideB_alt | (intros; apply _root_.GlobalTheory.TripInhab.isTriple_of_sideB_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerRatAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt in
theorem kerRatAt_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt := by
  intro hP hA hR hS
  refine (_root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt.and _root_.GlobalTheory.BigOn.Exp.twAdm_alt).imp fun Fm x hx i p hp hM w hw j hLT => ?_
  obtain ⟨l1, l2⟩ := hLT
  have h0 := _root_.GlobalTheory.T.ratHyp0_of_bad_prime_mem_S0 Fm x hx i p hp hM _ l2.2.2 l1 j
  obtain ⟨c', w', hw', hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.T.inGeo_half_of_ratHyp0 hP Fm x hx i p hp hM _ j h0)
  obtain ⟨S', YS', -⟩ := GlobalTheory.T.seriesRationality_back_from_movedReadings p.R p.cG p.Sx p.nexp w' hw'
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w').toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w' hw' h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w').toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w').phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w') (F2 p) B'.κ B'.v₀ B'.O ((Fm.ex x hx i).nch.twI w) j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  intro χ ξR ω φ hK h hh y hy u hu
  have hK' : KerDat (fullHeckeRealDatMovedReadings p.R w').toRealDat j ((fullHeckeRealDatMovedReadings p.R w').C.delAt (Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w))) χ ξR
      (placesOver (fullHeckeRealDatMovedReadings p.R w').toRealDat ((fullHeckeRealDatMovedReadings p.R w').mu ((Fm.D x i).plEq w)) (ownAt (Fm.D x i) ((Fm.D x i).plEq w)))
      ω φ := ⟨hK.chr, hK.fin, hK.triv, hK.tame, hK.pl, hK.off, hK.ram, hK.res, hK.weil, hK.vec⟩
  have hy' : InCoefLat (fullHeckeRealDatMovedReadings p.R w').toRealDat j h y := hy
  obtain ⟨x', hx'⟩ := kerRat_framed (T := setCE p.T c') hP hA hR hS YS' hRat (fun k => p.phsOne k) ((Fm.D x i).plEq w) hK' hh
    hy' u (by rw [hv]; exact hu)
  exact ⟨(p.R.FW j).ρ (w' j (sg0 _ p.P.A3.A)) x', hx'⟩
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Levels
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
theorem GlobalTheory.PenLev.levels_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∃ U0 : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), U0 ≤ GfC _ ∧ IsCompact (U0 : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → (∀ g ∈ U0, GlobalTheory.FinPl.Moves _ g (a.g.x j).L (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)) ∧ (∀ κ, GlobalTheory.FinPl.InK _ (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) κ → κ ∈ U0) ∧ ∀ α, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ U0 ∧ ∀ i, c i * _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hA j hj
  refine ⟨_root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj, _root_.GlobalTheory.PenLev.base_level_subgroup_le_gfc a j hj, _root_.GlobalTheory.T.is_compact_base_level_subgroup W hW u a ha hA j hj, fun t J hJ => ⟨_root_.GlobalTheory.T.true_geometry_tuple_free_moves_alt W hW u a ha hA j hj t J hJ, _root_.GlobalTheory.T.true_geometry_tuple_free_mem_alt W hW u a ha hA j hj t J hJ, fun α => ?_⟩⟩
  obtain ⟨c, hc, hmem⟩ := _root_.GlobalTheory.T.true_geometry_tuple_free_value_alt W hW u a ha hA j hj t J hJ α
  refine ⟨c, hc, fun g => ?_⟩
  rw [hmem g, _root_.GlobalTheory.T.true_geometry_tuple_free_relation_alt W hW u a ha hA j hj t J hJ α]
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTies
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GeoTies
set_option maxHeartbeats 1000000 in
theorem linked_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  intro hRF hL N S Γ hN hDiv
  have hE : _root_.GlobalTheory.PlugPt.HasExponent' N := (_root_.GlobalTheory.ExpTiesOfLayer.hasExp_of_layer_alt hL).2 N fun K B f T w Z Wt p0 t nch n xd c h =>
    (hN K B f T w Z Wt p0 t nch n xd c h).map Prod.fst
  let ν := _root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)
  have hRow := _root_.GlobalTheory.PlugPt.rowE_part_ties_alt hRF hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s ν (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (GlobalTheory.Plug.coreCondition_RX _ rfl)
  have hlink : ∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b → ∀ t : b.Comparison₂,
      linkOf (𝒮 := (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (fun K q c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K q c b.pt) K β c (b.part t) := by
    intro K β c b hl t
    obtain ⟨q, b', ⟨w⟩, e⟩ := hl
    have key : ∀ (x y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), x = y → ∀ t : x.2.2.Comparison₂, ∃ t' : y.2.2.Comparison₂,
        (⟨x.1, x.2.1, x.2.2.part t⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) = ⟨y.1, y.2.1, y.2.2.part t'⟩ := by
      rintro x _ rfl t
      exact ⟨t, rfl⟩
    obtain ⟨t', e'⟩ := key ⟨β.D, β.O, b⟩ _ e t
    exact ⟨q, b'.part t', _root_.GlobalTheory.T.exponent_reading_of_hasExp_bundle hL N S Γ hE K q c b' w t', e'⟩
  have hB : RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) GlobalTheory.PlugPt.RayPosition) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
      (fun _ D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) :=
    EvP.mono (fun _ K _ H β hq c b hl t => H β hq c (b.part t) (hlink K β c b hl t)) hRow
  have hR2 : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) :=
    ⟨GlobalTheory.PlugPt.RayPosition, GlobalTheory.Plug.largeBaseProperty_rayProperty hRF KPx _, RowE.row hB⟩
  obtain ⟨R, hR, hrow⟩ := RowL.and (KP := KPx) (Q := IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Q' := IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s)
    (Lk := _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) (H := AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition) hDiv hR2
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, hs⟩ := s Fm hc
  refine Built.ind (R := fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => _root_.GlobalTheory.Fc.R1.DivisorBundleCondition D O c b → (∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) → ∀ t : b.Comparison₂,
      _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) ?_ (hs x hx i).1 (H.1 Fm hc x hx i) (H.2 Fm hc x hx i)
  intro K β c b _ _ hl hdv hT
  have htw : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAll_pt β
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have key : ∀ y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, y = ⟨q.w.D q.Z, q.O, b'⟩ →
      DQ.TwAllAt y.1 y.2.1.ex.nch y.2.1.ex.xd → _root_.GlobalTheory.Fc.R1.DivisorBundleCondition y.1 y.2.1 c y.2.2 → (∀ t : y.2.2.Comparison₂,
        GlobalTheory.PlugPt.TiesB y.1 y.2.1 c (y.2.2.part t).pt ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt) →
      ∀ t : y.2.2.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands y.1 y.2.1 c (y.2.2.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (y.2.2.part t).pt ∧
        (y.2.2.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt := by
    rintro _ rfl htw hdv hT t
    obtain ⟨hTB, hRec, hMore⟩ := hT t
    have hcs := _root_.GlobalTheory.T.class_sum_divisibility_of_extensionWithLaw hL N S Γ hN K q c b' w t
    refine ⟨hcs.1, hcs.2 (_root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g _ hdv), ?_, hRec, hMore⟩
    exact _root_.GlobalTheory.PlugPt.ties_of_tiesB_alt _ _ c _ hTB hRec.1 (_root_.GlobalTheory.Fc.Ind.pt_realised_and_pb_eq _ _ c _).1 htw
  exact key ⟨β.D, β.O, b⟩ e htw hdv hT
end GlobalTheory.GeoTies
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCasesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_ref_of_decay_artin_ray_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.SerRefAlt := by
  first | exact @_root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class | exact _root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class | (intros; apply _root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class <;> assumption)
end
end

