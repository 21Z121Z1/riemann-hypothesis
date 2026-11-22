import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetAtUnram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.DetUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem det_mem_intAE (V : HSp D) (g : GA D V)
    (h : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V),
      finMat D.sp.cm.sig V.gram g *ᵥ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  obtain ⟨L, hL, hfg, hsp⟩ := GlobalTheory.SplitHeckeLabel.exists_coord_lattice V
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  rw [← hL] at h
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hfg hsp h

theorem part_mem_intAE {e d : AE D} (he : e * e = e) (hd : finPart D d ∈ intAE D) :
    finPart D (e * d + (1 - e)) ∈ intAE D := by
  have h1 : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])
  have h2 : finPart D (1 - e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul]; congr 1; linear_combination he)
  rw [RingHom.map_add, RingHom.map_mul]
  exact add_mem (GlobalTheory.SplitHeckeLabel.mul_mem_intA h1 hd) h2

theorem exists_isDetAt_unram : ∀ (D : D7) (V : HSp D) (ε : AF D.host.F) (e : AE D), IsSplitIdem D e → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∀ g ∈ KsphC V ∅, ∃ x, IsDetAt e V g x ∧ ∀ χ : (AE D)ˣ →* Circle, UnramAt ε χ → χ x = 1 := by
  intro D V ε e he hε g hg
  obtain ⟨h1, h0, -⟩ := he
  have hm : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  have hf : finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
    change (finHom V g).1 * (finHom V g⁻¹).1 = 1
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have i1 := det_mem_intAE V g fun y hy => (hg.2.1 y).1 hy
  have i2 := det_mem_intAE V g⁻¹ fun y hy => (hg.2.1 _).2 (by rw [Matrix.mulVec_mulVec, hf, Matrix.one_mulVec]; exact hy)
  generalize (Formalism.L2.Theta.mt V g⁻¹).det = d' at hd i2
  have hx : (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) * (e * d' + (1 - e)) = 1 := by
    linear_combination e * e * hd + (2 - (Formalism.L2.Theta.mt V g).det - d') * h1
  refine ⟨⟨_, _, hx, (mul_comm _ _).trans hx⟩, rfl, fun χ hχ => hχ _ ?_ (part_mem_intAE h1 i1) (part_mem_intAE h1 i2)⟩
  rw [← hε]
  change (e + cA D e) * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
  linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * h1 + ((Formalism.L2.Theta.mt V g).det - 1) * h0

end GlobalTheory.Mem.DetUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.ChainLevel

set_option maxHeartbeats 4000000 in

theorem chain_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ c : ChD D.what₂.Tup Φ D.R.m fun μ => (s μ).A, Nonempty (ChT y F.lv2 b rep (Top := fun μ => (s μ).A) (fun t x => ((tA (y.tup t)).cast (hA t)).j x) c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b m s tA hA
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HilbertLevels.spaces_hilbert D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hI hB
  obtain ⟨jX, hjX, htop⟩ := GlobalTheory.T.topSpaces_map_onto_chainTop_in_coordinates D G Pl0 I0 T A3 Ks R F cG hI hP hH y b m s tA hA
  obtain ⟨EE, Mult, mZ, mT, io, jE, jM, hEi, hEr, hEip, hM, hio0, hio, hioT, hjunk⟩ :=
    GlobalTheory.T.exists_hilbertChain_of_level_over_tops D (y.C F.lv2) b y.Us (fun μ => (s μ).A) jX D.R.two_le_m (h1 b).1 (h1 b).2 (h2 b) hjX
  obtain ⟨hsup, horth⟩ := GlobalTheory.T.rowFiniteTypeParts_span_and_orthogonal D G Pl0 I0 T A3 Ks R F cG hI hP hH y Φ rep hR b
  classical
  haveI : Finite Φ := hR.fin
  haveI : Fintype Φ := Fintype.ofFinite Φ
  have hle : ∀ π, y.prtE F.lv2 b (rep π) ≤ LinearMap.range jE := fun π => hEr ▸ hsup ▸ le_iSup (fun π => y.prtE F.lv2 b (rep π)) π
  let p : Φ → Submodule ℂ EE.T := fun π => (y.prtE F.lv2 b (rep π)).comap jE
  have hmap : ∀ π, (p π).map jE = y.prtE F.lv2 b (rep π) := fun π => Submodule.map_comap_eq_of_le (hle π)
  have hptop : (⨆ π, p π) = ⊤ := by
    apply Submodule.map_injective_of_injective hEi
    rw [Submodule.map_iSup, Submodule.map_top, hEr]
    simp only [hmap]
    exact hsup
  have hporth : ∀ π π', π ≠ π' → p π ⟂ p π' := by
    intro π π' hne
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [hEip]
    exact horth π π' hne _ hu _ hv
  obtain ⟨bs, ty, hft⟩ := GlobalTheory.Mem.exists_orthonormalBasis_adapted EE.T Φ p hptop hporth
  have hdisj : ∀ π π', π ≠ π' → y.prtE F.lv2 b (rep π) ⊓ y.prtE F.lv2 b (rep π') = ⊥ := by
    intro π π' hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hxE : x ∈ (y.C F.lv2).EEc b := hEr ▸ hle π hx1
    have h0 := horth π π' hne x hx1 x hx2
    by_contra hne0
    have := (h1 b).1.pos ⟨x, hxE⟩ (fun h => hne0 (by simpa using congrArg Subtype.val h))
    rw [h0] at this
    simp at this
  exact ⟨⟨EE, Mult, mZ, mT, io, _, bs, ty⟩, ⟨jE, jM, jX, hEi, hEr, hEip, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).1,
    fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.1, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.2,
    fun μ hμ => (hjX μ hμ).1, fun μ hμ => (hjX μ hμ).2.1, fun μ hμ => (hjX μ hμ).2.2, hio0, hio, hioT, hjunk,
    hft, hdisj, htop⟩⟩

end GlobalTheory.Mem.R3.Rw.ChainLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelElt

theorem one_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), ChiFin I l Z S → ∀ (P : SBof I a), P.1 ∈ I.Q a → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ (N : ℕ) (g₁ g₂ : GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z.1 = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z.1 ∧ ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g₁ * (show GA B (B.R.N i) from z.1) * g₂ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt | exact GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt | (intros; apply GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt <;> assumption)

theorem place_under : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : SBof I a), P.1 ∈ I.Q a → ∃ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∀ P' : SBof I a, P' ≠ P → ¬ Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P'.1) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.PlaceUnder.main | exact GlobalTheory.Mem.Col2.AdT.PlaceUnder.main | (intros; apply GlobalTheory.Mem.Col2.AdT.PlaceUnder.main <;> assumption)

theorem support_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)), (∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) → ∀ P : HeightOneSpectrum (𝓞 E), ¬ Formalism.L2.Col.IsOver v P → ∀ r s, adAt F P ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  first | exact @GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over | exact GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over | (intros; apply GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over <;> assumption)

theorem point_of_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → (∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s)) → ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  first | exact @GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat | exact GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat | (intros; apply GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat <;> assumption)

theorem mul_comp_eq {M N : Type} [Monoid M] [Monoid N] (f : M →* N) (y a b c k : M) (h : f b = f c) :
    f (y * (a * b) * k) = f (y * a * c * k) := by
  simp only [map_mul, h, mul_assoc]

theorem entry_eq_of_eq {M : Type} [Monoid M] {n : ℕ} {R : Type} [Semiring R] (f : M →* Matrix (Fin n) (Fin n) R) (b c : M)
    (h : f b = f c) (r s : Fin n) : f b r s = f c r s := by rw [h]

set_option maxHeartbeats 4000000 in

theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl), ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ x : (K (chOf c)).lev.U, (K (chOf c)).lev.chi x = (K (chOf c)).lev.chi κ ∧ (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c hChi κ
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = UAd B.sp.cm (B.R.N i) := by rw [hg]; rfl
  set y : GA B (B.R.N i) := ((K (chOf c)).y ⟨c, rfl⟩).1 with hy
  set kk : GA B (B.R.N i) := k (chOf c) with hkk
  have hsel : ∀ P : SBof I a, ∃ z : (K (chOf c)).lev.U, (K (chOf c)).lev.chi z = 1 ∧
      (∀ P' : SBof I a, P' ≠ P → ∀ r s, adAt B.host.F P'.1 (((show GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P'.1.adicCompletion B.fields.E)) r s) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) z.1 ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 ((((y * (show GA B (B.R.N i) from κ.1)) * (show GA B (B.R.N i) from z.1) * kk : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, hv'⟩ := place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := one_prime I hOk hPins l Z a _ i hi bad (K (chOf c)).lev hChi P hP v hv ((I.cst a).D P) (y * (show GA B (B.R.N i) from κ.1)) kk
      refine ⟨z, hz1, fun P' hP' r s => ?_, hz3, fun _ => hz4⟩
      have e := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P' z.1).1
      have h2 := hv' P' hP'
      rw [e] at h2
      exact support_one z.1 v hz2 P'.1 h2 r s
    · refine ⟨1, map_one _, fun P' _ r s => ?_, GlobalTheory.TwU.congAt_one _ _, fun h => absurd h hP⟩
      show adAt B.host.F P'.1 ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = _
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : (K (chOf c)).lev.U →* GA B (B.R.N i) := (K (chOf c)).lev.U.subtype
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := fun P P' h => Matrix.ext fun r s => by
    rw [cP_apply]; exact hzf2 P P' h r s
  have hlist : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : (K (chOf c)).lev.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlist _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hchiw : (K (chOf c)).lev.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hpt : ∀ g : GA B (B.R.N i), g ∈ UAd B.sp.cm (B.R.N i) → (∀ P ∈ I.Q a, ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) → ∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf g q :=
    fun g hg hr => point_of_rat B.sp.cm _ _ _ g hg hr
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨κ * w, ?_, ?_, ?_⟩
  · exact (map_mul (K (chOf c)).lev.chi κ w).trans ((congrArg _ hchiw).trans (mul_one _))
  · obtain ⟨p0, hp0, -⟩ := hR.k_std (chOf c)
    have hyU : y ∈ UAd B.sp.cm (B.R.N i) := eU ▸ ((K (chOf c)).y ⟨c, rfl⟩).2
    have hxU : (show GA B (B.R.N i) from (κ * w).1) ∈ UAd B.sp.cm (B.R.N i) := eU ▸ (((K (chOf c)).lev.U_eq _).1 (κ * w).2).1
    have hkU : kk ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
    refine hpt _ (mul_mem (mul_mem hyU hxU) hkU) fun P hP => ?_
    let P' : SBof I a := ⟨P, hQsub P hP⟩
    obtain ⟨γ, hγ⟩ := hzf4 P' hP
    refine ⟨γ, fun r s => ?_⟩
    have e1 := mul_comp_eq (cP P) y (show GA B (B.R.N i) from κ.1) (show GA B (B.R.N i) from w.1) (show GA B (B.R.N i) from (zf P').1) kk (hwP P')
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · intro P
    have e : κ.1⁻¹ * (κ * w).1 = w.1 := inv_mul_cancel_left κ.1 w.1
    refine (congrArg (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P)) e).mpr ?_
    refine ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P w.1).2.2).mpr fun r s => ?_
    have e := entry_eq_of_eq (cP P.1) _ _ (hwP P) r s
    have D2 := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P (zf P).1).2.2.1 (hzf3 P)) r s
    convert D2 using 3
    exact e

end GlobalTheory.Mem.Col2.AdT.LevelElt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftSpacesOverDefiniteForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

theorem GlobalTheory.LiftSpaces.exists_scaled_model {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (S : Submodule ℂ H) (n : ℕ) (hn : Module.finrank ℂ S = n) (a : ℝ) (ha : 0 < a) :
    ∃ E : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] H, Function.Injective E ∧ LinearMap.range E = S ∧
      (∀ x, ‖E x‖ ^ 2 = a * ‖x‖ ^ 2) ∧ ∀ x x', ⟪E x, E x'⟫_ℂ = (a : ℂ) * ⟪x, x'⟫_ℂ := by
  let b := (stdOrthonormalBasis ℂ S).reindex (finCongr hn)
  let c : ℂ := ((Real.sqrt a : ℝ) : ℂ)
  have hc0 : c ≠ 0 := by
    show ((Real.sqrt a : ℝ) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have hE : ∀ x, (c • (S.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap)) x = c • ((b.repr.symm x : S) : H) :=
    fun x => rfl
  refine ⟨c • (S.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap), ?_, ?_, ?_, ?_⟩
  · intro x x' h
    rw [hE, hE] at h
    exact b.repr.symm.injective (Subtype.ext (smul_right_injective H hc0 h))
  · rw [LinearMap.range_smul _ _ hc0, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
      Submodule.range_subtype]
  · intro x
    rw [hE, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      show ‖((b.repr.symm x : S) : H)‖ = ‖x‖ from b.repr.symm.norm_map x, mul_pow, Real.sq_sqrt ha.le]
  · intro x x'
    rw [hE, hE, inner_smul_left, inner_smul_right,
      show ⟪((b.repr.symm x : S) : H), ((b.repr.symm x' : S) : H)⟫_ℂ = ⟪x, x'⟫_ℂ from b.repr.symm.inner_map_map x x',
      ← mul_assoc]
    show (starRingEnd ℂ) ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) * _ = _
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]

theorem GlobalTheory.LiftSpaces.exists_thetaMap {D : D7} {C : ChainReal D} (L : LiftReal D C) (i : Fin D.R.m) (μ : D.what₂.Tup)
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (J : X →ₗ[ℂ] (GA D (L.V i) → L.TauV i)) (hJ : ∀ x, J x ∈ L.Amt μ i) (jM : Y →ₗ[ℂ] L.AmbW i)
    (hinj : Function.Injective jM) (hrange : LinearMap.range jM = L.Wc i)
    (hres : ∀ w ∈ L.MultW i, w ∘ₗ L.embK i = 0 → w = 0) :
    ∃ th : X →ₗ[ℂ] Y, ∀ x (h : J x ∈ L.Amt μ i) (w : L.AmbW i), w ∈ L.MultW i →
      w ∘ₗ L.embK i = L.thC μ i ⟨J x, h⟩ → L.eW i ∘ₗ w ∈ L.Wc i → jM (th x) = L.eW i ∘ₗ w := by
  classical
  let W2 : Submodule ℂ (L.AmbW i) := L.MultW i ⊓ (L.Wc i).comap (LinearMap.llcomp ℂ _ _ _ (L.eW i))
  let res : W2 →ₗ[ℂ] (L.TK i →ₗ[ℂ] (GA D (L.W i) → ℂ)) := LinearMap.lcomp ℂ _ (L.embK i) ∘ₗ W2.subtype
  have hker : LinearMap.ker res = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hres w.1 w.2.1 hw)
  obtain ⟨ψ, hψ⟩ := res.exists_leftInverse_of_injective hker
  let ev : W2 →ₗ[ℂ] L.Wc i :=
    ((LinearMap.llcomp ℂ _ _ _ (L.eW i)) ∘ₗ W2.subtype).codRestrict (L.Wc i) (fun w => w.2.2)
  let jinv : L.Wc i →ₗ[ℂ] Y :=
    (LinearEquiv.ofInjective jM hinj).symm.toLinearMap ∘ₗ (LinearEquiv.ofEq _ _ hrange.symm).toLinearMap
  refine ⟨jinv ∘ₗ ev ∘ₗ ψ ∘ₗ L.thC μ i ∘ₗ J.codRestrict (L.Amt μ i) hJ, ?_⟩
  intro x h w hw e hg
  have h1 : ψ (L.thC μ i ⟨J x, h⟩) = ⟨w, hw, hg⟩ := by
    rw [← e]
    exact LinearMap.congr_fun hψ ⟨w, hw, hg⟩
  have h2 : (ψ ∘ₗ L.thC μ i ∘ₗ J.codRestrict (L.Amt μ i) hJ) x = ⟨w, hw, hg⟩ := h1
  show jM ((LinearEquiv.ofInjective jM hinj).symm ((LinearEquiv.ofEq _ _ hrange.symm) (ev ((ψ ∘ₗ L.thC μ i ∘ₗ J.codRestrict (L.Amt μ i) hJ) x)))) = _
  rw [h2]
  rw [← LinearEquiv.ofInjective_apply (f := jM) (h := hinj), LinearEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.LiftSpaces.exists_lift_spaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (m : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G) (s : D.what₂.Tup → ℕ → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tL : ∀ μ j, Tie1 D.what₂.embLL (m μ j) (s μ j)) (hL : ∀ (i : Fin D.R.m) t, m (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t), ∃ l : LfD D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) D.what₂.Tup Φ fun μ j => (s μ j).A, Nonempty (LfT y F.lv2 rep (Mt := fun μ j => (s μ j).A) (fun i t x => ((tL (y.tup t) ((i : ℕ) + 1)).cast (hL i t)).j x) l) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO hI hP hH y Φ rep hR m s tL hL
  classical
  have hji : ∀ i : Fin D.R.m, 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ D.R.m := fun i => ⟨by omega, i.2⟩

  obtain ⟨d, hd1, hd0⟩ : ∃ d : ℕ → ℕ, (∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), d j = Module.finrank ℂ
      ((R.toRealDat.Wat ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap
        (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e)) ∧ ∀ j, ¬ (1 ≤ j ∧ j ≤ D.R.m) → d j = 0 :=
    ⟨fun j => if hj : 1 ≤ j ∧ j ≤ D.R.m then Module.finrank ℂ
      ((R.toRealDat.Wat ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap
        (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e) else 0,
      fun j hj => dif_pos hj, fun j hj => dif_neg hj⟩

  have hE : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), ∃ E : EuclideanSpace ℂ (Fin (d j)) →ₗ[ℂ]
      (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).H, Function.Injective E ∧
      LinearMap.range E = (R.toRealDat.Wat ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap
        (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e ∧
      (∀ x, ‖E x‖ ^ 2 = RealDat.nP F.lv2 false * ‖x‖ ^ 2) ∧
      ∀ x x', ⟪E x, E x'⟫_ℂ = ((RealDat.nP F.lv2 false : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
    intro j hj
    exact GlobalTheory.LiftSpaces.exists_scaled_model _ (d j) (hd1 j hj).symm _ (RealDat.nP_pos (F := F.lv2) false)
  choose EJ hEJ using hE

  let jMJ : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), EuclideanSpace ℂ (Fin (d j)) →ₗ[ℂ] (y.L F.lv2).AmbW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ :=
    fun j hj => (PiTensorProduct.lift : MultilinearMap ℂ (fun τ : D.what₂.Tau => (R.toRealDat.MW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).sm τ)
      (GA D (Wc D ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩) → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ (R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e ∘ₗ EJ j hj
  have hjM : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m), Function.Injective (jMJ j hj) ∧
      LinearMap.range (jMJ j hj) = (y.L F.lv2).Wc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∧
      ∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipWc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (jMJ j hj x) (jMJ j hj x') := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.liftHilbertModel_injective_contains_goodForms D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩
    obtain ⟨e1, e2, -, e4⟩ := hEJ j hj
    refine ⟨?_, ?_, ?_⟩
    · intro x x' hx
      exact e1 (h1 (PiTensorProduct.lift.injective hx))
    · ext z
      constructor
      · rintro ⟨x, rfl⟩
        have hx : EJ j hj x ∈ LinearMap.range (EJ j hj) := ⟨x, rfl⟩
        rw [e2] at hx
        exact Submodule.mem_map.2 ⟨_, hx, rfl⟩
      · intro hz
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hz
        obtain ⟨v, rfl⟩ := h2 hu
        have hv : v ∈ LinearMap.range (EJ j hj) := by rw [e2]; exact hu
        obtain ⟨x, rfl⟩ := hv
        exact ⟨x, rfl⟩
    · intro x x'
      show _ = (y.L F.lv2).ipWc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (PiTensorProduct.lift ((R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e (EJ j hj x)))
        (PiTensorProduct.lift ((R.toRealDat.HW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (sg0 D A3.A)).e (EJ j hj x')))
      rw [h3, e4, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (RealDat.nP_pos (F := F.lv2) false).ne',
        Complex.ofReal_one, one_mul]

  have hLat : ∀ j, ∃ Lt : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (EuclideanSpace ℂ (Fin (d j))),
      ∀ (hj : 1 ≤ j ∧ j ≤ D.R.m) x, x ∈ Lt.carrier ↔ ∃ v ∈ (R.toRealDat.FW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩).MK,
        v ∈ (R.toRealDat.FW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧
        EJ j hj x = (R.toRealDat.FW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩).j (sg0 D A3.A) v := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · obtain ⟨Lt, hLt⟩ := GlobalTheory.T.exists_goodIntegralForms_lattice_base_level D G Pl0 I0 T A3 Ks R F cG hO hI hP hH ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (EuclideanSpace ℂ (Fin (d j)))
        (EJ j hj) (hEJ j hj).1 (hEJ j hj).2.1
      exact ⟨Lt, fun _ x => hLt x⟩
    · refine ⟨⟨Finset.univ.image (EuclideanSpace.basisFun (Fin (d j)) ℂ), ?_⟩, fun hj' => absurd hj' hj⟩
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      simpa using (EuclideanSpace.basisFun (Fin (d j)) ℂ).toBasis.span_eq
  choose LatF hLatF using hLat

  have hUs : ∀ μ, y.Us μ → ∃ t, y.tup t = μ := by
    rintro μ (h | ⟨w, h⟩)
    · exact ⟨A3.A.μ0, y.tup0.trans h.symm⟩
    · exact ⟨_, h.symm⟩
  have eqn : ∀ j (hj : 1 ≤ j ∧ j ≤ D.R.m) t, m (y.tup t) j = lMat A3.A F.lv2.P0 F.lv2.ψ0 ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t :=
    fun j hj t => (congrArg (m (y.tup t)) (show j = (j - 1) + 1 by omega)).trans (hL ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t)

  have hMt : ∀ μ j (hj : 1 ≤ j ∧ j ≤ D.R.m), ∃ J : (s μ j).A.T →ₗ[ℂ]
      (GA D ((y.L F.lv2).V ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩) → (y.L F.lv2).TauV ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩),
      (y.Us μ → Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∧
        ∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (J x) (J x')) ∧
      ∀ t (h : y.tup t = μ) x, J (h ▸ ((tL (y.tup t) j).cast (eqn j hj t)).j x) =
        R.toRealDat.extV ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t (R.toRealDat.jV ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t x)) := by
    intro μ j hj
    by_cases hU : ∃ t, y.tup t = μ
    · obtain ⟨t0, rfl⟩ := hU
      have fo := ((tL (y.tup t0) j).cast (eqn j hj t0)).forms
      obtain ⟨J, h1, h2, h3, h4⟩ := GlobalTheory.T.liftDefiniteForms_eq_unitaryForms_classSumPairing D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ t0 (s (y.tup t0) j).A.T
        ((tL (y.tup t0) j).cast (eqn j hj t0)).j fo.li fo.span fo.inner
      refine ⟨J, fun _ => ⟨h1, h2, h3⟩, ?_⟩
      intro t h x
      have ht : t = t0 := by
        have := congrArg y.tupT h
        rwa [y.tupT_tup, y.tupT_tup] at this
      subst ht
      exact h4 x
    · refine ⟨0, fun hμ => absurd (hUs μ hμ) hU, fun t h _ => absurd ⟨t, h⟩ hU⟩
  choose JM hJM using hMt

  have hTh : ∀ μ j (hj : 1 ≤ j ∧ j ≤ D.R.m), ∃ f : (s μ j).A.T →ₗ[ℂ] EuclideanSpace ℂ (Fin (d j)), y.Us μ →
      ∀ x (h : JM μ j hj x ∈ (y.L F.lv2).Amt μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩) (w : (y.L F.lv2).AmbW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩),
        w ∈ (y.L F.lv2).MultW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ →
        w ∘ₗ (y.L F.lv2).embK ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ = (y.L F.lv2).thC μ ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ⟨JM μ j hj x, h⟩ →
        (y.L F.lv2).eW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∘ₗ w ∈ (y.L F.lv2).Wc ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ →
        jMJ j hj (f x) = (y.L F.lv2).eW ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ ∘ₗ w := by
    intro μ j hj
    by_cases hμ : y.Us μ
    · obtain ⟨f, hf⟩ := GlobalTheory.LiftSpaces.exists_thetaMap (y.L F.lv2) ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ μ (JM μ j hj)
        (fun x => ((hJM μ j hj).1 hμ).2.1 ▸ LinearMap.mem_range_self _ x) (jMJ j hj) (hjM j hj).1 (hjM j hj).2.1
        (GlobalTheory.T.lowestKType_restriction_injective_on_multiplicity D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose TH hTH using hTh
  refine ⟨{ Mj := fun j => ⟨EuclideanSpace ℂ (Fin (d j))⟩
            lat := LatF
            th := fun μ j => if hj : (1 ≤ j ∧ j ≤ D.R.m) ∧ y.Us μ then TH μ j hj.1 else 0
            isot := fun j π => if hj : 1 ≤ j ∧ j ≤ D.R.m then
              (y.prtW F.lv2 ⟨j - 1, Nat.lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.one_pos) hj.2⟩ (rep π)).comap (jMJ j hj) else ⊥ }, ⟨{
    eW := fun i => EJ ((i : ℕ) + 1) (hji i)
    eW_range := fun i => (hEJ ((i : ℕ) + 1) (hji i)).2.1
    eW_norm := fun i x => (hEJ ((i : ℕ) + 1) (hji i)).2.2.1 x
    eW_lat := fun i x => hLatF ((i : ℕ) + 1) (hji i) x
    jMj := fun i => jMJ ((i : ℕ) + 1) (hji i)
    jMj_read := fun i v => rfl
    jMj_inj := fun i => (hjM ((i : ℕ) + 1) (hji i)).1
    jMj_range := fun i => (hjM ((i : ℕ) + 1) (hji i)).2.1
    jMj_ip := fun i => (hjM ((i : ℕ) + 1) (hji i)).2.2
    jMt := fun μ i => JM μ ((i : ℕ) + 1) (hji i)
    jMt_inj := fun μ hμ i => ((hJM μ ((i : ℕ) + 1) (hji i)).1 hμ).1
    jMt_range := fun μ hμ i => ((hJM μ ((i : ℕ) + 1) (hji i)).1 hμ).2.1
    jMt_ip := fun μ hμ i => ((hJM μ ((i : ℕ) + 1) (hji i)).1 hμ).2.2
    theta := ?_
    junk := ?_
    out := ?_
    isot := ?_
    disj := fun i π π' h => GlobalTheory.T.goodForms_nonisomorphicTypeParts_inf_eq_bot D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y Φ rep hR i π π' h
    read := fun i t _ x => (hJM (y.tup t) ((i : ℕ) + 1) (hji i)).2 t rfl x }⟩⟩
  · intro μ hμ i x h w hw e hg
    show jMJ ((i : ℕ) + 1) (hji i) ((if hj : (1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ D.R.m) ∧ y.Us μ then TH μ ((i : ℕ) + 1) hj.1 else 0) x) = _
    rw [dif_pos ⟨hji i, hμ⟩]
    exact hTH μ ((i : ℕ) + 1) (hji i) hμ x h w hw e hg
  · intro μ hμ j
    show (if hj : (1 ≤ j ∧ j ≤ D.R.m) ∧ y.Us μ then TH μ j hj.1 else 0) = 0
    rw [dif_neg (fun h => hμ h.2)]
  · intro j hj
    show Subsingleton (EuclideanSpace ℂ (Fin (d j)))
    rw [hd0 j (by omega)]
    exact ⟨fun a b => PiLp.ext fun k => k.elim0⟩
  · intro i π v
    show v ∈ (if hj : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ D.R.m then
      (y.prtW F.lv2 ⟨(i : ℕ) + 1 - 1, by omega⟩ (rep π)).comap (jMJ ((i : ℕ) + 1) hj) else ⊥) ↔ _
    rw [dif_pos (hji i)]
    exact Iff.rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowsDatum_prescribedTuples_definedWeights : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | exact GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | (intros; apply GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistedOpenExponentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_open_exponent : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  first | exact @GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel | exact GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel | (intros; apply GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel <;> assumption)
end

