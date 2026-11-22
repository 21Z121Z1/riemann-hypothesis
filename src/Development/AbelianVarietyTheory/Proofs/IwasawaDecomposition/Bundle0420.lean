import Mathlib
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0007
import Formalism.LocalRingCardinality.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0411
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0412
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue
import Formalism.LocalToGlobal.Divisibility.QLocTied

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TiePlace

theorem iota_sigma_mem_range {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (S : HidaSetting p n' W Qq O Kf ι σ j w) (s : ℕ) (y : Qq) :
    ι ((σ ^ s) y) ∈ Set.range (algebraMap O Kf) ↔ y ∈ Set.range (algebraMap W Qq) := by
  haveI := S.frac_alt
  haveI := S.frac_O

  have h1 : ∀ z : Qq, z ∈ Set.range (algebraMap W Qq) → σ z ∈ Set.range (algebraMap W Qq) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := S.frob t
    exact ⟨_, ht'.symm⟩
  have hk : ∀ (k : ℕ) (z : Qq), z ∈ Set.range (algebraMap W Qq) → (σ ^ k) z ∈ Set.range (algebraMap W Qq) := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      rw [pow_succ]
      exact ih _ (h1 z hz)
  have hs : ∀ z : Qq, (σ ^ s) z ∈ Set.range (algebraMap W Qq) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, hk s z⟩
    have hn : 1 ≤ n' := le_trans (by norm_num) S.two_le
    have e : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = z := by
      have em : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = (σ ^ (s * (n' - 1)) * σ ^ s) z := rfl
      rw [em, ← pow_add]
      have : s * (n' - 1) + s = n' * s := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [this, pow_mul, S.period, one_pow]
      rfl
    rw [← e]
    exact hk _ _ h

  have hj : Function.Injective j := by
    intro a b h
    apply IsFractionRing.injective W Qq
    apply ι.injective
    rw [S.ι_comp, S.ι_comp, h]
  have hnu : ¬ IsUnit (p : O) := by
    letI := j.toAlgebra
    haveI : Module.Finite W O := S.finite
    haveI : FaithfulSMul W O := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    intro h
    exact S.p_unif.not_isUnit ((isUnit_map_iff (algebraMap W O) _).1 (by simpa using h))
  have hι : ∀ z : Qq, ι z ∈ Set.range (algebraMap O Kf) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, ?_⟩
    · by_contra hz
      obtain ⟨o, ho⟩ := h
      have hz0 : z ≠ 0 := fun h0 => hz ⟨0, by rw [h0, map_zero]⟩
      obtain ⟨t, ht⟩ := (ValuationRing.isInteger_or_isInteger W z).resolve_left hz
      have htu : ¬ IsUnit t := by
        rintro ⟨u, rfl⟩
        apply hz
        refine ⟨(u⁻¹ : Wˣ), ?_⟩
        rw [← inv_inv z, ← ht]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      have htm : t ∈ Ideal.span {(p : W)} := by
        rw [← S.p_unif.maximalIdeal_eq]
        exact htu
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 htm
      have e1 : algebraMap O Kf (o * j (t' * p)) = 1 := by
        rw [map_mul, ho, ← S.ι_comp, ht, ← map_mul, mul_inv_cancel₀ hz0, map_one]
      have e2 : o * j (t' * p) = 1 := by
        apply IsFractionRing.injective O Kf
        rw [e1, map_one]
      apply hnu
      have : IsUnit (j (t' * p)) := IsUnit.of_mul_eq_one o (by rw [mul_comm]; exact e2)
      rw [map_mul, map_natCast] at this
      exact isUnit_of_mul_isUnit_right this
    · rintro ⟨t, rfl⟩
      exact ⟨j t, (S.ι_comp t).symm⟩
  rw [hι, hs]

theorem val_pos_iff {K : Type} [Field K] (val : AddValuation K (WithTop ℤ)) (z : K) :
    (0 : WithTop ℤ) < val z ↔ z = 0 ∨ ¬ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, false_or, AddValuation.map_inv, not_le]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, val z = n := WithTop.ne_top_iff_exists.1 (fun h => hz ((AddValuation.top_iff val).1 h)) |>.imp fun _ h => h.symm
    rw [hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    norm_cast
    omega

theorem mem_asIdeal_iff_inv {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (x : R) :
    x ∈ v.asIdeal ↔ x = 0 ∨ (algebraMap K (v.adicCompletion K) (algebraMap R K x))⁻¹ ∉ v.adicCompletionIntegers K := by
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx, false_or, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, not_le]
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
    have h1 : (algebraMap K (v.adicCompletion K) (algebraMap R K x)) = ((algebraMap R K x : K) : v.adicCompletion K) := rfl
    rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have h0 : v.valuation K (algebraMap R K x) ≠ 0 := by
      simpa using hx
    rw [one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem inv_int_iff {p : ℕ} {G : GAtP p} (v : Fin G.P.nV) (s : ℕ) {LL : Type} [Field LL]
    (val : AddValuation LL (WithTop ℤ)) (emb : LL →+* G.Kf)
    (hint : ∀ z, (0 : WithTop ℤ) ≤ val z ↔ emb z ∈ Set.range (algebraMap G.O G.Kf)) (z : LL) (y : G.P.Qq v)
    (hk : emb z = G.P.ι v ((G.P.σ v ^ s) y)) :
    y⁻¹ ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  rw [hint, map_inv₀, hk, ← map_inv₀, ← map_inv₀]
  exact (iota_sigma_mem_range (G.P.setting v) s y⁻¹).symm

section Comparison₂

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem tie_mem_iff {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) (v : Fin G.P.nV) (x : 𝓞 F) :
    x ∈ (t.pl v).1.asIdeal ↔ x = 0 ∨
      ((t.eQ v _ rfl).symm ((t.spl _ (t.pl v).2 (inclE (F := F) ((t.pl v).1.adicCompletion F) (algebraMap F E (x : F)))).1))⁻¹ ∉
        Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
  rw [t.spl_F, mem_asIdeal_iff_inv (K := F), t.completion_integers_iff v _ rfl, map_inv₀, RingEquiv.apply_symm_apply]

end Comparison₂

theorem int_map_eq_zero_iff {F E L : Type} [Field F] [Field E] [Field L] (g : F →+* E) (f : E →+* L)
    (x : 𝓞 F) : f (g (x : F)) = 0 ↔ x = 0 := by
  rw [map_eq_zero_iff f f.injective, map_eq_zero_iff g g.injective]
  exact RingOfIntegers.coe_eq_zero_iff

set_option maxHeartbeats 4000000 in

theorem place_of_tie : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  intro D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hpos := pos_C D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s
    (algebraMap D.host.F D.host.E (x : D.host.F))
  have hsig : sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F)) =
      algebraMap D.host.F D.host.E (x : D.host.F) := AlgHom.commutes _ _
  have key : (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
      (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) =
      ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v (algebraMap D.host.F D.host.E (x : D.host.F)))) := by
    have e : tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F)) = Cmp.tEL (recC D sc Ce Lc I ψ hd)
          ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩) (if Even s.val then algebraMap D.host.F D.host.E (x : D.host.F)
            else sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F))) := by
      by_cases he : Even s.val
      · simp only [he, if_true, ite_true, ↓reduceIte]; rfl
      · simp only [he, if_false, ite_false, ↓reduceIte, hsig]; rfl
    rw [e]
    exact hpos
  refine (tie_mem_iff ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) v x).trans ?_
  have hz : x = 0 ↔ tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)) = 0 := by
    exact (int_map_eq_zero_iff (algebraMap D.host.F D.host.E) (Cmp.tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)) x).symm
  refine Iff.trans ?_ (val_pos_iff (D.what₂.places.val w) (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)))).symm
  exact or_congr hz (not_congr (inv_int_iff v s.val (D.what₂.places.val w) ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg)
    ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW_int u w hg) _ _ key))

end GlobalTheory.TiePlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrameStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedSelfDualLattice_iff_integral_stdFrame : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V 1 Λ 1 → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.Mem.SDFrameStd.lamHat_iff_int | exact GlobalTheory.Mem.SDFrameStd.lamHat_iff_int | (intros; apply GlobalTheory.Mem.SDFrameStd.lamHat_iff_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardCodeWordStagesFiniteGroupEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.Mem.CyclotomicFieldContainment

theorem natCard_codeWordStages_finiteGroup_eq (X : Stages) : Nat.card (G0g X.toD7.nd) = X.B.restRowsFiniteGroupCard := by
  have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
  rw [Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
  rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
  rfl

theorem rootsField_le_iff (X : Stages) {N : IntermediateField ℚ ℂ} :
    rootsField X.B.toPre ≤ N ↔ ∀ n ∈ rootOrders X.toD7, cycField n ≤ N := by
  simp only [rootsField, rootOrders, natCard_codeWordStages_finiteGroup_eq, sup_le_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_assoc]
  rfl

theorem rootOrders_ne_zero (X : Stages) : ∀ n ∈ rootOrders X.toD7, n ≠ 0 := by
  have hg : ∀ k, X.toD7.host.g k * (X.toD7.host.g k - 1) ≠ 0 := fun k => by
    have hp := X.toD7.host.g_prime k
    exact mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  simp only [rootOrders, natCard_codeWordStages_finiteGroup_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨X.B.restRowsFiniteGroupCard_pos.ne', hg 0, hg 1, by norm_num, by norm_num⟩

variable (ι : Qb →+* ℂ)

theorem le_map_of_qb_le {A : IntermediateField ℚ ℂ} {Y : Fld} (hA : ∀ z ∈ A, ∃ x, ι x = z) (h : qb ι A ≤ Y) :
    A ≤ Y.map ι.toRatAlgHom := fun z hz => by
  obtain ⟨x, rfl⟩ := hA z hz
  exact ⟨x, h (mem_qb.2 hz), rfl⟩

theorem muFld_le_qb {n : ℕ} (hn : n ≠ 0) {N : IntermediateField ℚ ℂ} (h : cycField n ≤ N) : muFld n ≤ qb ι N := by
  rw [muFld, IntermediateField.adjoin_le_iff]
  intro x hx
  refine mem_qb.2 (h (mem_cycField hn ?_))
  rw [← map_pow, show x ^ n = 1 from hx, map_one]

theorem cycField_le_map {n : ℕ} (hn : n ≠ 0) {Y : Fld} (hY : muFld n ≤ Y) (hz : ∃ x, ι x = rootOne n) :
    cycField n ≤ Y.map ι.toRatAlgHom := by
  obtain ⟨x, hx⟩ := hz
  refine cycField_le_iff.2 ⟨x, hY (IntermediateField.subset_adjoin ℚ _ ?_), hx⟩
  apply ι.injective
  rw [map_pow, hx, map_one]
  exact (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

variable {E : Type} [Field E] [NumberField E]

theorem valsOf_subset_qb {χ : HChar E} {s : ℝ} {N : IntermediateField ℚ ℂ} (h : valueField χ s ≤ N) :
    valsOf ι s χ ⊆ qb ι N := fun _ ⟨v, hv, e⟩ =>
  mem_qb.2 (h (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, e⟩))

theorem valueField_le_map {χ : HChar E} {s : ℝ} {Y : Fld} (hY : valsOf ι s χ ⊆ Y)
    (hz : ∀ z ∈ valueField χ s, ∃ x, ι x = z) : valueField χ s ≤ Y.map ι.toRatAlgHom := by
  rw [valueField, IntermediateField.adjoin_le_iff]
  rintro z ⟨v, hv, rfl⟩
  obtain ⟨x, hx⟩ := hz _ (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, rfl⟩)
  exact ⟨x, hY ⟨v, hv, hx⟩, hx⟩

theorem ksQ_eq (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (hx : X.B.KsExact δ f) (T : HostTied X.toD7)
    (P : KsPieces X.toD7 T) (hR : P.rcf = qb T.fr.ι δ.ray) (hM : P.M = qb T.fr.ι δ.M) (hD : P.MDel = qb T.fr.ι δ.M')
    (hK : P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j)) :
    KsQ X.toD7 T (Fr.at X f) P = qb T.fr.ι (listField δ f) := by
  have hran : ∀ z ∈ listField δ f, ∃ x, T.fr.ι x = z := by
    intro z hz
    have hz' : z ∈ X.B.KsC := by rw [show X.B.KsC = listField δ f from hx]; exact hz
    obtain ⟨x, -, rfl⟩ := hz'
    exact ⟨T.jLL x, T.embLL x⟩
  have hle : ∀ {A : IntermediateField ℚ ℂ}, A ≤ listField δ f → ∀ z ∈ A, ∃ x, T.fr.ι x = z :=
    fun h z hz => hran z (h hz)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (listField_le_iff δ f).1 le_rfl
  have hKP : (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) ≤ listField δ f :=
    iSup₂_le fun j hj => h6 j hj.1 hj.2
  have hroots := (rootsField_le_iff X).1 h4
  have hne := rootOrders_ne_zero X
  simp only [charField, sup_le_iff, iSup_le_iff] at h5
  obtain ⟨⟨⟨⟨hmu, heta⟩, hdel⟩, hdel'⟩, hom⟩ := h5
  apply le_antisymm
  · have hM' : P.M ≤ qb T.fr.ι (listField δ f) := by
      rw [hM]
      exact fun x hx => mem_qb.2 (h2 (δ.M_le_M' hx))
    simp only [KsQ, sup_le_iff, iSup_le_iff]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hM'⟩, ?_⟩, ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact mem_qb.2 (h1 ⟨a, (T.fr.phi0 a).symm⟩)
    · exact fun n hn => muFld_le_qb _ (hne n hn) (hroots n hn)
    · rw [valsFld, IntermediateField.adjoin_le_iff]
      rintro x (((hx | hx) | hx) | hx)
      · obtain ⟨j, hx⟩ := Set.mem_iUnion.1 hx
        exact valsOf_subset_qb _ (hmu j) hx
      · exact valsOf_subset_qb _ heta hx
      · exact valsOf_subset_qb _ hdel hx
      · exact valsOf_subset_qb _ hdel' hx
    · rw [hR]; exact fun x hx => mem_qb.2 (h3 hx)
    · rw [hD]; exact fun x hx => mem_qb.2 (h2 hx)
    · rw [hK]; exact fun x hx => mem_qb.2 (hKP hx)
  · obtain ⟨Y, hYe⟩ : ∃ Y, Y = KsQ X.toD7 T (Fr.at X f) P := ⟨_, rfl⟩
    have hY : KsQ X.toD7 T (Fr.at X f) P ≤ Y := hYe.ge
    rw [← hYe]
    simp only [KsQ, sup_le_iff, iSup_le_iff] at hY
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, a6⟩, a7⟩ := hY
    have ha3 : ∀ {A : Set Qb}, A ⊆ valsFld X.toD7 T (Fr.at X f) → A ⊆ Y := fun h _ hx => a3 (h hx)
    have hv : (⋃ j, valsOf T.fr.ι 0 ((Fr.at X f).mu0 j)) ∪ valsOf T.fr.ι (1 / 2) (Fr.at X f).eta ∪
        valsOf T.fr.ι 0 (Fr.at X f).del ∪ valsOf T.fr.ι 0 (Fr.at X f).del' ⊆ Y :=
      ha3 (IntermediateField.subset_adjoin ℚ _)
    have hr : rootsField X.B.toPre ≤ Y.map T.fr.ι.toRatAlgHom := (rootsField_le_iff X).2 fun n hn =>
      cycField_le_map _ (hne n hn) (a2 n hn) (hran _ (hroots n hn (IntermediateField.mem_adjoin_simple_self ℚ _)))
    have hmap : listField δ f ≤ Y.map T.fr.ι.toRatAlgHom := by
      refine (listField_le_iff δ f).2 ⟨?_, ?_, ?_, hr, ?_, fun j hj hj' => ?_⟩
      · rintro _ ⟨a, rfl⟩
        exact ⟨T.fr.j a, a1 ⟨a, rfl⟩, T.fr.phi0 a⟩
      · exact le_map_of_qb_le _ (hle h2) (hD ▸ a6)
      · exact le_map_of_qb_le _ (hle h3) (hR ▸ a4)
      · simp only [charField, sup_le_iff, iSup_le_iff]
        refine ⟨⟨⟨⟨fun j => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, hx⟩))))) (hle (hmu j))
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inr hx)))) (hle heta)
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inr hx))) (hle hdel)
        · exact valueField_le_map _ (fun x hx => hv (Or.inr hx)) (hle hdel')
        · rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨k, a, rfl⟩
          exact hr (om_mem_rootsField f k a)
      · refine le_map_of_qb_le _ (hle (h6 j hj hj')) fun x hx => a7 ?_
        rw [hK]
        exact mem_qb.2 ((le_iSup₂_of_le j ⟨hj, hj'⟩ le_rfl : δ.KPsi j ≤ ⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) hx)
    intro x hx
    obtain ⟨y, hy, e⟩ := hmap hx
    have hyx : y = x := T.fr.ι.injective e
    exact hyx ▸ hy

theorem oTied_of_ksExact : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre)
    (δ : FieldDat X.B.toPre), X.B.KsExact δ f → ∀ T : HostTied X.toD7, ∃ O : OTied X.toD7 T (Fr.at X f),
      O.pieces.rcf = qb T.fr.ι δ.ray ∧ O.pieces.MDel = qb T.fr.ι δ.M' := by
  intro hA hW X f δ hx T
  obtain ⟨P, -, hR, hM, hD, hK⟩ := GlobalTheory.T.exists_smallField_classFieldPieces hA hW X f δ T
  have hq := ksQ_eq X f δ hx T P hR hM hD hK
  refine ⟨⟨P, X.B.OtoLL_injective, fun x => ?_⟩, hR, hD⟩
  rw [hq]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨mem_qb.2 ?_, (X.toD7.O_int y).map T.jLL.toIntAlgHom⟩
    rw [T.embLL, ← show X.B.KsC = listField δ f from hx]
    exact ⟨_, (algebraMap (𝓞 X.B.Ks) X.B.Ks y).2, rfl⟩
  · rintro ⟨hxq, hi⟩
    have hz : T.fr.ι x ∈ X.B.KsC := by
      rw [show X.B.KsC = listField δ f from hx]
      exact hxq
    obtain ⟨w, hw, e⟩ := hz
    have hwx : T.jLL w = x := T.fr.ι.injective ((T.embLL w).trans e)
    subst hwx
    have hwi : IsIntegral ℤ w := (isIntegral_algHom_iff T.jLL.toIntAlgHom T.jLL.injective).1 hi
    obtain ⟨y, hy⟩ := X.B.O_full w hw hwi
    exact ⟨y, congrArg T.jLL hy⟩

end GlobalTheory.Mem.CyclotomicFieldContainment

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoOfEquivariantHomIntoIsotypicSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_iso_of_equivariantHom_into_isotypicSum : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), σ0.IsIrreducible → σ.IsIrreducible → ∀ f ∈ homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g), f ≠ 0 → Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
  first | exact @GlobalTheory.IsoRankMult.iso_of_hom_into_sum | exact GlobalTheory.IsoRankMult.iso_of_hom_into_sum | (intros; apply GlobalTheory.IsoRankMult.iso_of_hom_into_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonzeroLiftPartTypeGivesNonzeroTypeVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.IsotPartVec

attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem actM_of_mult {D : D7} {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : Mult.MMap M} (hT : T ∈ Mult.Mult θ M J χ)
    (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : P.ψ κ ∈ J) : principalLevelFrame.actM P M κ T = χ (P.ψ κ) • T := by
  apply MultilinearMap.ext
  intro v
  funext g
  rw [principalLevelFrame.actM_apply, principalLevelFrame.mult_lev hT v _ hκ g]
  rfl

theorem exists_typeVec_of_isotL {D : D7} {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (h : principalLevelFrame.isotL θ P M J χ e π ≠ ⊥) :
    ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x := by
  obtain ⟨T, hT, hT0⟩ := (Submodule.ne_bot_iff _).1 h
  have hTg : T ∈ Mult.goodPart θ M J χ e := (Submodule.mem_inf.1 hT).1
  have hTi : T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π := (Submodule.mem_inf.1 hT).2
  have hTm : T ∈ Mult.Mult θ M J χ := (Submodule.mem_inf.1 hTg).1
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.isotIn_detect_by_eqv_map D (Mult.MMap M) (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π T hTi hT0
  refine ⟨q T, (hq T hTi).1, hq0, fun κ hκ => ?_⟩
  rw [← (hq T hTi).2 κ, actM_of_mult P M hTm κ hκ, map_smul]

theorem main : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (i : Fin D.R.m), principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) π ≠ ⊥ → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((Y.PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) ((Y.PW i).ψ κ)) x := by
  intro _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y _ _ π i h
  exact exists_typeVec_of_isotL _ _ _ _ _ _ π h

end GlobalTheory.IsotPartVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankEquivariantHomsIntoIsotypicSumOfIsoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_equivariantHomsInto_isotypicSum_of_iso : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) → Module.rank ℂ (homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g)) = Module.rank ℂ (homInto σ0 ρ C) := by
  first | exact @GlobalTheory.MultIso.rank_homInto_iSup_range | exact GlobalTheory.MultIso.rank_homInto_iSup_range | (intros; apply GlobalTheory.MultIso.rank_homInto_iSup_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormClassSum_principal_eq_card_mul_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P),
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  first | exact @GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | exact GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | (intros; apply GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValueStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singleBlock_doublingIntegral_value : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ ν : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → IsNu P ν → ∀ r t : ℕ, 1 ≤ t → StepAt P δ (fun _ => ν) r t 0 (zVal1 (qP P) r t : ℂ) := by
  first | exact @GlobalTheory.Mem.SingleQ.stepAt_one | exact GlobalTheory.Mem.SingleQ.stepAt_one | (intros; apply GlobalTheory.Mem.SingleQ.stepAt_one <;> assumption)
end

