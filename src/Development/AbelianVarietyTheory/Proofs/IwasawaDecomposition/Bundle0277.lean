import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetOfKer
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RefCharValues

theorem exists_finset_of_ker {G C : Type} [CommGroup G] [Group C] [Finite C] (f : G →* ℂ) (cl : G →* C)
    (S₀ : Finset ℂ) (h₀ : ∀ z ∈ S₀, IsAlgebraic ℚ z)
    (hk : ∀ F : Subfield ℂ, (∀ z ∈ S₀, z ∈ F) → ∀ x, cl x = 1 → f x ∈ F) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) → ∀ x, f x ∈ F := by
  classical
  haveI := Fintype.ofFinite C
  let r : C → G := Function.invFun cl
  refine ⟨S₀ ∪ Finset.univ.image fun c => f (r c), fun z hz => ?_, fun F hF x => ?_⟩
  · rcases Finset.mem_union.1 hz with h | h
    · exact h₀ z h
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h
      have h1 := hk (algebraicClosure ℚ ℂ).toSubfield (fun z hz => mem_algebraicClosure_iff.2 (h₀ z hz))
        (r c ^ Nat.card C) (by rw [map_pow, pow_card_eq_one'])
      rw [map_pow] at h1
      exact IsAlgebraic.of_pow Nat.card_pos (mem_algebraicClosure_iff.1 h1)
  · have h1 : cl (r (cl x)) = cl x := Function.invFun_eq ⟨x, rfl⟩
    have h2 := hk F (fun z hz => hF z (Finset.mem_union_left _ hz)) (x * (r (cl x))⁻¹)
      (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    have h3 : f (r (cl x)) ∈ F :=
      hF _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩))
    have h4 := mul_mem h2 h3
    rwa [← map_mul, inv_mul_cancel_right] at h4

theorem exists_finset_emb (E : Type) [Field E] [NumberField E] :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) →
      ∀ (φ : E →+* ℂ) (x : E), φ x ∈ F := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), fun z hz => ?_,
    fun F hF φ x => ?_⟩
  · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b p.2)).algHom p.1.toRatAlgHom
  · rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def]
    exact mul_mem (SubfieldClass.ratCast_mem F _) (hF _ (Finset.mem_image.2 ⟨(φ, i), Finset.mem_univ _, rfl⟩))

theorem exists_principal (L : Type) [Field L] [NumberField L] (a : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (h1 : ClassGroup.mk L ((GlobalTheory.Mem.UnitIndex.idealHom L).toHomUnits a) = 1) : ∃ e : Lˣ, ∀ v, Valued.v
      ((a * (FiniteAdeleRing.unitEmbedding (𝓞 L) L e)⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ).1 v) = 1 := by
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  refine ⟨Units.mk0 x hx0, (GlobalTheory.Idele.smul_eq_self_iff (R := 𝓞 L) (K := L) _ (I := 1) one_ne_zero).1 ?_⟩
  rw [GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, GlobalTheory.Idele.idealOf_unitEmbedding, hx']
  exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)

theorem exists_class (D : D7) : ∃ cl : (AE D)ˣ →* ClassGroup (𝓞 D.host.E), ∀ x, cl x = 1 → ∃ e : D.host.Eˣ,
    finPart D ((x * (Units.map (incA D).toMonoidHom e)⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧
    finPart D (((x * (Units.map (incA D).toMonoidHom e)⁻¹)⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  let φ : (AE D)ˣ →* (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom
  refine ⟨(ClassGroup.mk D.host.E).comp ((GlobalTheory.Mem.UnitIndex.idealHom D.host.E).toHomUnits.comp φ), fun x hx => ?_⟩
  obtain ⟨e, he⟩ := exists_principal D.host.E (φ x) hx
  have hφ : φ (Units.map (incA D).toMonoidHom e) = FiniteAdeleRing.unitEmbedding (𝓞 D.host.E) D.host.E e :=
    Units.ext (h1 e)
  rw [← hφ, ← map_inv, ← map_mul] at he
  refine ⟨e, ?_⟩
  generalize x * (Units.map (incA D).toMonoidHom e)⁻¹ = u at he
  refine ⟨(h2 _).2 fun P => (he P).le, (h2 _).2 fun P => ?_⟩
  have h3 : (φ u).1 P * (φ u⁻¹).1 P = 1 := by
    have : (φ u).1 * (φ u⁻¹).1 = 1 := by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) this
  have h4 := congrArg Valued.v h3
  rw [map_mul, he P, one_mul, map_one] at h4
  exact h4.le

theorem sign_zpow_even (z : ℂ) (h : z ≠ 0) (k : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * k) = (z / starRingEnd ℂ z) ^ k := by
  rw [zpow_mul]
  congr 1
  have h1 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using h
  rw [zpow_ofNat, div_pow, h1]
  field_simp

theorem exists_finset_char (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq c χ)
    {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (k : I → ℤ) (hi : χ.HasInf φ fun i => 2 * k i) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) →
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ F := by
  classical
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  obtain ⟨N, -, -, m, hm, hm1⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1.1
  obtain ⟨cl, hcl⟩ := exists_class D
  obtain ⟨S₁, hS₁, hE⟩ := exists_finset_emb D.host.E
  obtain ⟨S, hS, h⟩ := exists_finset_of_ker (Circle.coeHom.comp (c.comp b)) cl
    (S₁ ∪ Polynomial.nthRootsFinset m (1 : ℂ))
    (fun z hz => by
      rcases Finset.mem_union.1 hz with h | h
      · exact hS₁ z h
      · refine IsAlgebraic.of_pow hm ?_
        rw [(Polynomial.mem_nthRootsFinset hm _).1 h]
        exact isAlgebraic_one)
    (fun F hF x hx => by
      obtain ⟨e, he1, he2⟩ := hcl x hx
      have hF1 := hE F fun z hz => hF z (Finset.mem_union_left _ hz)
      let y : (AE D)ˣ := Units.map (incA D).toMonoidHom e
      have hu : FinUnit (b (x * y⁻¹)) := ⟨(hb _).1, by rw [(hb _).2]; exact he1, by rw [← map_inv, (hb _).2]; exact he2⟩
      have h1 : ((c (b (x * y⁻¹)) : Circle) : ℂ) ∈ F :=
        hF _ (Finset.mem_union_right _ ((Polynomial.mem_nthRootsFinset hm _).2 (by
          rw [← Circle.coe_pow, hm1 _ hu, Circle.coe_one])))
      have h2 : ((c (a y) : Circle) : ℂ) ∈ F := by
        rw [GlobalTheory.HeckeInfExp.eq_inf D c χ hc e _ _ (hab _) (hb _).1 (hb _).2, hi e]
        refine prod_mem fun i _ => ?_
        rw [sign_zpow_even _ ((map_ne_zero _).2 e.ne_zero)]
        exact zpow_mem (div_mem (hF1 _ _) (hF1 ((starRingEnd ℂ).comp (φ i)) _)) _
      have h3 : c (a y) * c (b y) = 1 := by rw [← map_mul, ← hab y]; exact hc.1.2 e
      have h4 : c (b x) = c (b (x * y⁻¹)) * (c (a y))⁻¹ := by
        rw [← eq_inv_of_mul_eq_one_right h3, ← map_mul, ← map_mul, inv_mul_cancel_right]
      show ((c (b x) : Circle) : ℂ) ∈ F
      rw [h4, Circle.coe_mul, Circle.coe_inv]
      exact mul_mem h1 (inv_mem h2))
  refine ⟨S, hS, fun F hF x hx => ?_⟩
  have h1 : b x = x := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _ ((hb x).1.trans hx.symm) (hb x).2)
  have h2 : ((c (b x) : Circle) : ℂ) ∈ F := h F hF x
  rwa [h1] at h2

theorem exists_finset_values : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) → ∀ (i : Fin D.R.m) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ F := by
  intro D T0 L μ0 hL
  classical
  have key : ∀ i : Fin D.R.m, ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) →
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ F := by
    intro i
    obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
    choose z hz using fun g => (D.hc (D.eTau.symm g)).e_int i
    refine exists_finset_char D _ _ (hL.mu0 i) (Formalism.L2.Host.embPsi D.host) (fun g => -z g) ?_
    have : n = fun g => 2 * -z g := funext fun g => by
      have h1 := hn g
      simp only [Formalism.L2.Host.eExp, hz] at h1
      exact_mod_cast h1
    rwa [this] at hi
  choose S hS h using key
  refine ⟨Finset.univ.biUnion S, fun z hz => ?_, fun F hF i => h i F fun z hz => hF z ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hS i z hi
  · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩

end GlobalTheory.RefCharValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.Half

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 1600000 in

theorem preChar_updFW {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)
    (h : PreChar R) : PreChar (updFW R nW FW) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

section Upd

variable (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)

set_option maxHeartbeats 1600000 in

def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    OMDat T.toCore (updFW R nW FW) i Tp tup := { O with }

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in
theorem omPins_upd (i : Fin D.R.m) (h : OMPins T R κ v₀ O i) :
    OMPins T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

set_option maxHeartbeats 1600000 in
theorem fired_upd (ph : Fin D.R.m → ℂ) (h : Fired T R κ v₀ O ph) :
    Fired T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) ph :=
  ⟨fun i => h.1 i, fun i σ hσ hV => h.2 i σ hσ hV⟩

end Upd

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in

def tieGeo (h : TieIn T R κ v₀) : FWTie T (geoR T R κ v₀ O) κ v₀ :=
  let t := tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ)
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

set_option maxHeartbeats 1600000 in
theorem barTie_tieGeo (h : TieIn T R κ v₀) : BarTie (tieGeo T R κ v₀ O h) :=
  fun i σ hσ hV => barTie_tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ) i σ hσ hV

set_option maxHeartbeats 1600000 in
theorem rhoGeo_tieGeo (h : TieIn T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) :
    RhoGeo (tieGeo T R κ v₀ O h) (fun i => updO T R _ _ (O i)) := by
  intro i
  have hb := hasB_nTop T h.laws κ i
  refine ⟨fun hk g f => ?_, fun hk g => ?_⟩
  · have hex := GlobalTheory.LevelRep.exists_cusp_rep T κ i (O i).lev2 h.laws (hp i).2.act.1 hk
    refine ⟨hk g f f.2, ?_⟩
    have e1 : geoRho T R κ O i = rhoB D.what₂.LL hb.some hex.choose := dif_pos ⟨hb, hex⟩
    have e2 : (⟨_, hk g f f.2⟩ : Cu T κ i) = hex.choose g f := Subtype.ext (hex.choose_spec g f).symm
    show crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) ⟨_, hk g f f.2⟩ =
      geoRho T R κ O i g (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) f)
    rw [e1, e2, crdOr_eq hb, rhoB_crd]
  · have e1 : geoRho T R κ O i = 1 := dif_neg fun h' => hk fun g f hf => by
      have h1 := h'.2.choose_spec g ⟨f, hf⟩
      have h2 := (h'.2.choose g ⟨f, hf⟩).2
      rw [h1] at h2
      exact h2
    show geoRho T R κ O i g = 1
    rw [e1]
    rfl

set_option maxHeartbeats 1600000 in
theorem chiIs_chiTop_of_tie (hL : R.toLevCh.Is A.μ0) (h : TieIn T R κ v₀) (i : Fin D.R.m) : ChiIs R i (chiTop R i) := by
  choose y ha using GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL h i
  have hne : ∀ g, algebraMap T.Q.c.F D.what₂.LL (y g) ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 _ (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.RealGeo.Half

namespace GlobalTheory.RealGeo

set_option maxHeartbeats 1600000 in

theorem exists_geoHalf_geoR : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O ph hc ht hp hf
  have hf' := Half.fired_upd T R κ v₀ (nTop T κ) (formsGeo T R κ v₀ O) O ph hf
  refine ⟨⟨κ, v₀, Half.tieGeo T R κ v₀ O ht, Half.barTie_tieGeo T R κ v₀ O ht, fun i => Half.updO T R _ _ (O i),
    fun i => Half.omPins_upd T R κ v₀ _ _ O i (hp i), Half.rhoGeo_tieGeo T R κ v₀ O ht hp,
    fun i σ hσ hV _ => hf'.2 i σ hσ hV, fun i _ => ⟨ph i, hf'.1 i⟩, fun i _ _ => hf'.1 i⟩,
    rfl, rfl, hf', Half.preChar_updFW R _ _ hc, fun i g => ?_⟩
  exact (Half.chiIs_chiTop_of_tie T R κ v₀ hc.lev ht i g).trans (Units.coe_prod _ _)

end GlobalTheory.RealGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilDatumOOfRankEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilOriented

theorem exists_isWeilDatumO_of_rank_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  intro D ψ hψ V W χ χ' om ha hw
  have hr : V.rank ≤ W.rank := ha.1.le
  obtain ⟨e, hc, hcs, he, hrat, hsm, hheis, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr
  let E : (WA V W → ℂ) ≃ₗ[ℂ] (WO V W → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv
  obtain ⟨omO, hom⟩ := exists_extend (ThS ψ V W) E om
  have hom' : ∀ p (Φ : ThS ψ V W), omO p (fun x => Φ.1 (e x)) = fun x => (om p Φ).1 (e x) := hom
  have hsurj : ∀ f, IsThetaFunO ψ V W f → ∃ Φ : ThS ψ V W, f = fun x => Φ.1 (e x) := fun f hf => by
    have e1 : f = fun x => (fun y => f (e.symm y)) (e x) := by funext x; simp
    refine ⟨⟨fun y => f (e.symm y), mem_ThS.2 ((hth ψ _).1 ?_)⟩, e1⟩
    rw [← e1]; exact hf
  have hTh : ∀ Φ : ThS ψ V W, IsThetaFunO ψ V W fun x => Φ.1 (e x) := fun Φ => (hth ψ _).2 (mem_ThS.1 Φ.2)
  have hact : ∀ g h x, e (actO V W g h x) = actHom V W g h (e x) := fun g h x => by
    rw [he, he]; exact (GlobalTheory.OrientedSmall.bridgeSmall D V W hr).2 g h x
  refine ⟨omO, ⟨hψ, ha.2.1.1, ha.2.2.1.1, ha.2.2.2.1, ha.2.2.2.2, fun p f hf => ?_, fun g h w₀ f hf => ?_,
    fun γ hγ γ' hγ' f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_,
    fun ε hε g h hg hh x y hx hy => ?_⟩, fun p Φ => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']; exact hTh _
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    let Φ' : ThS ψ V W := ⟨Heisenberg₂ ψ V W (e w₀) Φ.1,
      mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis hψ (mem_ThS.1 Φ.2) _)⟩
    rw [hheis, hom', hheis, hact, ← hw.Heisenberg₂ g h (e w₀) Φ Φ' rfl]
    exact hom' _ Φ'
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    simp only [map_zero]
    exact hw.aut γ hγ γ' hγ' Φ
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    simp only [hom']
    exact hw.cont Φ (e w)
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨j1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D V W
    have : BorelSpace (WA V W) := ⟨rfl⟩
    have : BorelSpace (WO V W) := ⟨rfl⟩
    obtain ⟨ν, hν, hF, hint⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WO V W) e.symm hcs
      (by simpa using hc) (ratL V W) (ratL W V) (fun x => by rw [← hrat, e.apply_symm_apply]) μ 𝓕 hμ h𝓕
    refine lintegral_eq_of_integral_eq (ratL W V) hK hcov (hTh _).cont (hTh _).cont (norm_periodic hψ (hTh _))
      (norm_periodic hψ (hTh _)) hμ h𝓕 ?_
    rw [← hint, ← hint]
    simp only [e.apply_symm_apply]
    exact hw.unit ν _ hν hF p Φ
  · obtain ⟨r, hr0, hℓ⟩ := hw.split ε hε g h hg hh x y hx hy
    refine ⟨r, hr0, fun ℓ hinv f hf => ?_⟩
    obtain ⟨Φ, rfl⟩ := hsurj f hf
    have := hℓ (ℓ ∘ₗ E.toLinearMap ∘ₗ (ThS ψ V W).subtype) (fun u hu Ψ Ψ' hΨ => ?_) Φ
    · rw [hom']
      unfold splitFac at this
      rw [if_pos hr] at this
      exact this
    · have hu' : cA D ε • e.symm u = e.symm u := by
        apply e.injective
        rw [hsm, e.apply_symm_apply]
        exact Matrix.ext hu
      have := hinv (e.symm u) (fun i j => congrFun (congrFun hu' i) j) _ (hTh Ψ)
      rw [hheis, e.apply_symm_apply, ← hΨ] at this
      exact this
  · simp only [← he]
    exact hom' p Φ

end GlobalTheory.Mem.WeilOriented
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LevFinCong

variable {D : D7}

theorem finE_mem_UA (V : HSp D) (κ : GA D V) : finE V κ ∈ UA D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have := (GlobalTheory.Mass.swapPts (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π κ)).2
  rwa [GlobalTheory.Mass.coe_swapPts, hπ κ] at this

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen ((((Kg D.sp.cm V.gram β T).comap
      ((Formalism.UG.bc (swapAE D)).comp (Bridge.Gf V).subtype)) : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hc : Continuous ((Bridge.Gf V).subtype) := continuous_subtype_val
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β T hc (map_one _)] with x hh
  obtain ⟨h2, h3⟩ := hh
  obtain ⟨g, hg⟩ := x.2
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ UA D.sp.cm V.gram := by
    rw [← hg]; exact finE_mem_UA V g
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem exists_finCong_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ levS V β L ∧ levChi V β L k = 1 := by
  classical
  intro D V β L
  obtain ⟨N, hN, hK⟩ := GlobalTheory.SplitRepsOpen.exists_finCong_le D V _ (isOpen_comap_Kg V β (L.Pg ∪ L.Q))
  refine ⟨N, hN, fun k hf hk => ?_⟩
  have hk' : finE V k ∈ Kg D.sp.cm V.gram β (L.Pg ∪ L.Q) := hK k hk
  refine ⟨⟨hf, ?_⟩, ?_⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk'
  · unfold levChi
    rw [GlobalTheory.GoodFiniteDim.levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk', Units.val_one]

end GlobalTheory.LevFinCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMemLattice
section
namespace GlobalTheory.NatSmulMemLattice

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ (n : ℕ) (a : 𝓞 E), 0 < n ∧ (a : E) = (n : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ ((y : E) * (y • c)) := by
    have h3 : IsIntegral ℤ (y : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y))
    exact h3.mul hy
  refine ⟨y.natAbs * y.natAbs, ⟨_, h2⟩, ?_, ?_⟩
  · have := Int.natAbs_pos.2 hy0
    positivity
  · have h4 : ((y.natAbs * y.natAbs : ℕ) : E) = (y : E) * (y : E) := by
      have h5 : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
      have h6 := congrArg (Int.cast : ℤ → E) h5
      rw [Int.cast_natCast, Int.cast_mul] at h6
      exact h6
    rw [h4]
    change (y : E) * (y • c) = _
    rw [zsmul_eq_mul, mul_assoc]

theorem exists_nat_smul_mem {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (L : Submodule (𝓞 E) W)
    (hL : Submodule.span E (L : Set W) = ⊤) (v : W) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 E) • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set W) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨n, e, hn, he⟩ := exists_nat_mul_integral c
    refine ⟨a * n, Nat.mul_pos ha hn, ?_⟩
    have key : ((a * n : ℕ) : 𝓞 E) • c • x = e • (a : 𝓞 E) • x := by
      rw [← algebraMap_smul E e, ← algebraMap_smul E (a : 𝓞 E),
        ← algebraMap_smul E ((a * n : ℕ) : 𝓞 E), smul_smul, smul_smul]
      congr 1
      have he' : algebraMap (𝓞 E) E e = (n : E) * c := he
      rw [he', map_natCast, map_natCast, Nat.cast_mul]
      ring
    rw [key]
    exact L.smul_mem _ hx

theorem exists_nat_smul_mem_lattice {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (v : Formalism.BasicNotions.HSpace.V V) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 (Formalism.BasicNotions.D7.host D).E) • v ∈ Formalism.BasicNotions.HSpace.L0 V :=
  exists_nat_smul_mem _ V.standardTuple_isLattice.span_eq_top v

end GlobalTheory.NatSmulMemLattice
end

