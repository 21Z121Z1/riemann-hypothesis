import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
section
noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ArInt GlobalTheory.Mean4O GlobalTheory.CxPts

namespace GlobalTheory.Mean4O.ReadsProj

section Local

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (σ : k →+* ℂ)

def HalfWeight (L : HermLB p) (g : CxPts p σ → CxPts p σ → ℝ) : Prop :=
  ∀ x, ∃ i, x ∈ ptsIn p σ (L.B.U i) ∧ ∀ z, (L.φ σ).φ i z / 2 = g x z

variable {σ} {L L' : HermLB p} {g g' : CxPts p σ → CxPts p σ → ℝ}

theorem HalfWeight.congr (h : HalfWeight σ L g) (e : ∀ x z, g x z = g' x z) : HalfWeight σ L g' := by
  rwa [← show g = g' from funext₂ e]

theorem halfWeight_locPot (L : HermLB p) : HalfWeight σ L (L.φ σ).locPot.φ :=
  fun x => ⟨_, (L.φ σ).locPot.mem_U x, fun _ => rfl⟩

theorem halfWeight_triv : HalfWeight σ (HermLB.triv p) fun _ _ => 0 :=
  fun _ => ⟨PUnit.unit, mem_ptsIn_top, fun _ => zero_div _⟩

theorem halfWeight_fnB (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu hc) :
    HalfWeight σ (fnB u hu hc) fun _ z => u σ z / 2 :=
  fun _ => ⟨PUnit.unit, mem_ptsIn_top, fun _ => rfl⟩

theorem HalfWeight.tens (h : HalfWeight σ L g) (h' : HalfWeight σ L' g') :
    HalfWeight σ (L.tens L') fun x z => g x z + g' x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  obtain ⟨j, hj, e'⟩ := h' x
  exact ⟨(i, j), mem_ptsIn_inf.2 ⟨hi, hj⟩, fun z => (add_div _ _ _).trans (congrArg₂ (· + ·) (e z) (e' z))⟩

theorem HalfWeight.dual (h : HalfWeight σ L g) : HalfWeight σ L.dual fun x z => -g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  exact ⟨i, hi, fun z => (neg_div _ _).trans (congrArg (-·) (e z))⟩

theorem HalfWeight.pow (h : HalfWeight σ L g) (m : ℕ) : HalfWeight σ (L.pow m) fun x z => m * g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  refine ⟨fun _ => i, CxPts.mem_pow_iff.2 hi, fun z => ?_⟩
  refine (congrArg (· / 2) ((L.φ σ).zpow_φ m _ z)).trans ?_
  simp only [← e z, mul_div_assoc, Int.cast_natCast]

theorem HalfWeight.zp (h : HalfWeight σ L g) (n : ℤ) : HalfWeight σ (zp L n) fun x z => n * g x z :=
  ((h.pow n.toNat).tens (h.pow (-n).toNat).dual).congr fun x z => by
    have e : ((n.toNat : ℤ) : ℝ) - ((-n).toNat : ℤ) = n := by exact_mod_cast Int.toNat_sub_toNat_neg n
    rw [← e]
    simp only [Int.cast_natCast]
    ring

theorem halfWeight_comb {ι : Type} [Fintype ι] {L : ι → HermLB p} {g : ι → CxPts p σ → CxPts p σ → ℝ}
    (h : ∀ i, HalfWeight σ (L i) (g i)) (n : ι → ℤ) :
    HalfWeight σ (ArInt.comb L n) fun x z => ∑ i, n i * g i x z := by
  have key (l : List ι) : HalfWeight σ (l.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p))
      fun x z => (l.map fun i => n i * g i x z).sum := by
    induction l with
    | nil => exact halfWeight_triv
    | cons i l ih => exact ((h i).zp (n i)).tens ih
  exact (key _).congr fun x z => Finset.sum_map_toList _ _

end Local

open ProjSpace

variable (N : ℕ)

abbrev σ₀ : ℤ →+* ℂ := Int.castRingHom ℂ

abbrev rd : AnRead (PSpace.str ℤ N) σ₀ N := AnRead.all _ _ N

theorem isAlg : IsAlgAtlas (ProjAn.finAtlas ℤ σ₀ N) := (rd N).isAlgAtlas_finAtlas

abbrev om : LocPot (CxPts (PSpace.str ℤ N) σ₀) :=
  ((ProjAn.fsO1 ℤ σ₀ N).pull (𝟙 _) (Category.id_comp _)).locPot

theorem om_pot : IsPotential (ProjAn.finAtlas ℤ σ₀ N) (om N) :=
  (ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ (rd N)).isPotential (isAlg N)

theorem om_pos : IsPosPot (ProjAn.finAtlas ℤ σ₀ N) (om N) :=
  ((ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ (rd N)).isPosPot_iff (isAlg N)).2 (ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos _ _ (rd N))

theorem fs_pot : IsPotential (ProjAn.finAtlas ℤ σ₀ N) ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot :=
  ((hermitianTwistingSheaf ℤ N).isSmooth (rd N)).isPotential (isAlg N)

theorem om_sameForm : SameForm (ProjAn.finAtlas ℤ σ₀ N) (om N) ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot :=
  Weight.sameForm_of_eq _ (isAlg N) (fs_pot N) fun x =>
    ⟨fun _ => _, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 (((hermitianTwistingSheaf ℤ N).φ σ₀).locPot.mem_U x)), fun z => by
      refine (congrArg (· / 2) (Weight.pull_φ _ _ _ _ _)).trans ?_
      have e : Points.PtsOver.map (𝟙 _) (Category.id_comp (PSpace.str ℤ N)) _ z = z := Subtype.ext (Category.comp_id _)
      erw [e]
      rfl⟩

def man : Man N where
  n := 0
  X _ := CxPts (PSpace.str ℤ N) σ₀
  cpt _ := (isArithVar_int N).compactSpace _
  t2 _ := CxPts.t2Space_cxPts_of_isProjOver _ (isArithVar_int N).isProjOver
  ne _ := ⟨Points.projPt σ₀ ⟨fun _ => 1, by
    rw [Ideal.eq_top_iff_one]; exact Ideal.subset_span ⟨0, rfl⟩⟩⟩
  A _ := ProjAn.finAtlas ℤ σ₀ N
  Z _ := ∅
  r _ _ := Real.exp 1
  Om _ := om N
  bd _ := InhabCalc.isBd_empty _ _ (om_pot N) (om_pos N)
  κ := 1
  κ_pos := one_pos

theorem man_int (P : Fin N → (man N).Pot) (u : (man N).Fun) :
    (man N).int P u = mInt (ProjAn.finAtlas ℤ σ₀ N) (fun i => P i (0 : Fin 1)) (u (0 : Fin 1)) :=
  (one_mul _).trans (Fin.sum_univ_one _)

def pts (σ : ℤ →+* ℂ) : CxPts (PSpace.str ℤ N) σ → (man N).X 0 :=
  cast (congrArg (CxPts (PSpace.str ℤ N)) (Subsingleton.elim σ σ₀))

theorem smooth_iff (u : CxPts (PSpace.str ℤ N) σ₀ → ℝ) :
    (ProjAn.finAtlas ℤ σ₀ N).Smooth u ↔ ∀ y, CInfAt u y := by
  rw [(isAlg N).smooth_iff (rd N), ← CxPts.cInfAt_iff_smoothOn (rd N) isOpen_univ]
  simp

def calc₀ : Calc (man N) :=
  InhabCalc.calcOf (man N) (fun (_ : Unit) _ => ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot) fun _ _ => fs_pot N

def cls₀ (i : Unit) : (calc₀ N).V := InhabCalc.cls (man N) _ (fun _ _ => fs_pot N) i

theorem chernOn : (calc₀ N).ChernOn (fun _ => 0) (pts N) 1 (fun _ : Unit => hermitianTwistingSheaf ℤ N) (cls₀ N) := by
  intro u hs hu hc n f hf
  have := (isArithVar_int N).compactSpace σ₀
  have := CxPts.t2Space_cxPts_of_isProjOver σ₀ (isArithVar_int N).isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ₀ (isArithVar_int N).isProjOver
  rw [one_mul, man_int, chInt, finsum_eq_single _ σ₀ fun σ h => absurd (Subsingleton.elim _ _) h]
  refine (ChernMA.chernInt_eq_mInt (HermLB.cInf _ _) (isAlg N) (projLine_continuous_of_smooth _ (hf 0))).trans ?_
  refine SameForm.mInt_eq (fun _ => Weight.sameForm_of_eq _ (isAlg N) ((calc₀ N).firstChern_isPotential _ 0) ?_) _
  refine (halfWeight_comb (σ := σ₀) (g := fun o : Option Unit => o.elim (fun _ z => u 0 z)
    fun _ => ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot.φ) (fun o => ?_) n).congr fun x z => ?_
  · cases o with
    | none => exact (halfWeight_fnB _ hu hc).congr fun x z => mul_div_cancel_left₀ _ two_ne_zero
    | some i => exact halfWeight_locPot _
  · have e : (InhabCalc.smProj (man N) u : (man N).Fun) = u := InhabCalc.smProj_of_smooth _ hs
    rw [Fintype.sum_option, Fintype.sum_unique, Fintype.sum_unique]
    change _ = ∑ i : Unit, ((n (some ()) : ℝ) * @Pi.single Unit (fun _ => ℝ) _ (fun _ _ => Classical.propDecidable _) () 1 i + (n none : ℝ) * 0) *
      ((hermitianTwistingSheaf ℤ N).φ σ₀).locPot.φ x z + ((n (some ()) : ℝ) * 0 +
        (n none : ℝ) * (InhabCalc.smProj (man N) u : (man N).Fun) 0 z)
    rw [e]
    simp [add_comm]

theorem reads_proj_of (N : ℕ) (H : (calc₀ N).ChernOn (fun _ => 0) (pts N) 1 (fun _ : Unit => hermitianTwistingSheaf ℤ N) (cls₀ N) →
      ∃ (K : Calc (man N)) (v : Unit → K.V),
        (∀ i σ, LeviEq ((man N).A σ) (K.c1 (v i) σ) ((calc₀ N).c1 (cls₀ N i) σ)) ∧
        K.ChernOn (fun _ => 0) (pts N) 1 (fun _ : Unit => hermitianTwistingSheaf ℤ N) v ∧
        @Calc.NumOn N (man N) ℤ _ _ (PSpace.str ℤ N) K (fun _ => 0) (pts N) 1 Unit _ (fun _ => hermitianTwistingSheaf ℤ N) v
          (isArithVar_int N).isIntegral) :
    ∃ (M : Man N) (K : Calc M) (ε : (ℤ →+* ℂ) → Fin (M.n + 1))
    (π : ∀ σ, CxPts (PSpace.str ℤ N) σ → M.X (ε σ)) (v : Unit → K.V), (∀ σ, Function.Injective (π σ)) ∧
    0 < M.int (fun _ => K.c1 (v ())) (fun _ _ => 1) ∧
    @Calc.Reads N M ℤ _ _ (PSpace.str ℤ N) K ε π 1 Unit _ (fun _ => GlobalTheory.ProjSpace.hermitianTwistingSheaf ℤ N) v
      (GlobalTheory.ProjSpace.isArithVar_int N).isIntegral := by
  obtain ⟨K, v, h₁, h₂, h₃⟩ := H (chernOn N)
  refine ⟨man N, K, fun _ => 0, pts N, v, fun σ => ?_, ?_, isArithVar_int N, one_pos, fun σ => ?_,
    fun j => ⟨σ₀, Subsingleton.elim (α := Fin 1) _ _⟩, fun u hu σ => ?_, h₂, h₃⟩
  · obtain rfl : σ = σ₀ := Subsingleton.elim _ _
    exact Function.injective_id
  · refine lt_of_lt_of_eq (InhabCalc.int_Om_pos (man N) ⟨0, inferInstance⟩) ?_
    rw [man_int, man_int]
    refine (SameForm.mInt_eq (fun _ => om_sameForm N) _).trans (Eq.symm ?_)
    refine (LeviOnly.mInt_eq_of_leviEq N ((man N).X 0) ((man N).A 0) _ _ _ (fun _ => K.firstChern_isPotential _ 0)
      (fun _ => (calc₀ N).firstChern_isPotential (cls₀ N ()) 0) (fun _ => h₁ () 0)).1.trans ?_
    exact InhabCalc.mInt_congr_φ _ (fun _ => InhabCalc.first_chern_class_potential (man N) _ (fun _ _ => fs_pot N) () 0) _
  · obtain rfl : σ = σ₀ := Subsingleton.elim _ _
    exact ⟨continuous_id, Function.surjective_id⟩
  · obtain rfl : σ = σ₀ := Subsingleton.elim _ _
    exact (smooth_iff N _).1 (hu 0)

end GlobalTheory.Mean4O.ReadsProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOfHeisInv
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

theorem inv_of_heisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = l φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl g hg φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a')) v
  have htadd : ∀ f f' : (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      tens (evFin F v) (f + f') R = tens (evFin F v) f R + tens (evFin F v) f' R := fun f f' => by
    funext x; simp [tens, add_mul]
  have htsmul : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) R = c • tens (evFin F v) f R := fun c f => by
    funext x; simp [tens, mul_assoc]
  let Sop : UA σ G.V'.J → (((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) :=
    fun g =>
    { toFun := fun f t => (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i))
      map_add' := fun f f' => by
        funext t; simp only [htadd, map_add, Pi.add_apply]; ring
      map_smul' := fun c f => by
        funext t; simp only [htsmul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hSop : ∀ g f t, Sop g f t = (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) :=
    fun _ _ _ => rfl
  have huniq : ∀ (T : ((Fin a' × Fin (a + a') → AF F) → ℂ) → (Fin a' × Fin (a + a') → AF F) → ℂ)
      (f f₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ SB _ → Acts (evFin F v) T f f₁ →
      ∀ t, f₁ t = (R 0)⁻¹ * T (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro T f f₁ hf hA t
    rw [hA R (hR f hf)]
    have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
    have h1 : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR f hf).1 0 _ hat
    simp only [tens, h1, GlobalTheory.LatVac.evFin_liftV]
    field_simp
  have hS : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Sop g f ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, 1)) f (Sop g f) := by
    intro g hg f hf
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v g hg
    have e : S₀ f = Sop g f := funext fun t => (huniq _ f _ hf (hS₀ f hf).2 t).trans (hSop g f t).symm
    rw [← e]; exact hS₀ f hf
  obtain ⟨φ₀, hφ₀, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v (hT.base.inert v w hin).2.2 m C hC
  by_cases hz : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), l f = 0
  · rw [hz φ₁ hφ₁, hz φ hφ]
  push_neg at hz
  have hl0 : l φ₀ ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hz; exact hne (hline l hl h f hf)
  let c : UA σ G.V'.J → ℂ := fun g => l (Sop g φ₀) / l φ₀
  have hlaw : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ f₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) f f₁ → l f₁ = c g * l f := by
    intro g hg f hf f₁ hf₁ hA
    have hf₁eq : f₁ = Sop g f := funext fun t => (huniq _ f f₁ hf hA t).trans (hSop g f t).symm
    have hE := GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator F E σ B a a' G X om om' hT v m C l hl g hg (Sop g) (hS g hg)
    have hl' : GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ Sop g - c g • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hE u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (l ∘ₗ Sop g - c g • l) φ₀ = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, c]
      field_simp
      ring
    have h1 := hline _ hl' h0 f hf
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h1
    rw [hf₁eq]
    linear_combination h1
  have hc := GlobalTheory.T.inert_place_transforming_character_eq_one F E σ B a a' G X om om' hT v w hin hv m C hC l hl hz c hlaw g hg
  rw [hlaw g hg φ hφ φ₁ hφ₁ hA, hc, one_mul]

end GlobalTheory.InertVacLag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isBig_of_smul_cls_eq_add_ampleAt : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  intro hnum k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x _ ha e hx hn₂
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = q.appTop ((Scheme.ΓSpecIso (.of k)).inv r) :=
    algebraΓOfHom_algebraMap q
  have hp : IsProjOver (strHom k X) := (strHom_eq hf) ▸ hq
  obtain ⟨m, A, s, hm, hA, hAmp, hxs⟩ := hx
  have hD := Semi.LB.isLB_div (isLB_lbPow h₁ m) hA
  have hsec : HasNonzeroSec (LB.div (lbPow N₁ m) A) := ⟨s, sec_ne_zero_of_mem hxs⟩
  have hB : IsBig k (tens (lbPow N₂ m) A) := (hn₂.pow hAmp m).isBig_tens_ample hnum hp hAmp
  have hP := isLB_lbPow hN (a * m)
  have e₂ : (a * m) • cls N hN = m • (cls N₁ h₁ + cls N₂ h₂) := by
    rw [← e, smul_smul, mul_comm a m]
  have hbig : IsBig k (lbPow N (a * m)) := hB.of_cls_eq_add hf hq hD hsec hP (by
    rw [cls_tens (isLB_lbPow h₂ m) hA, cls_div (isLB_lbPow h₁ m) hA hD, cls_lbPow hN, cls_lbPow h₂,
      cls_lbPow h₁, e₂]
    module)
  exact hbig.of_pow hN (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' hm.ne'))
    fun n => finite_coh_zero_twist_of_isProjOver hf hq (isLB_lbPow hN n)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSectionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHecke_productOfLocalTestFunctions_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → IsHecke (globLev S K') (globFn S f) := by
  first | exact @GlobalTheory.BCT.GlobHecke.isHecke_globFn | exact GlobalTheory.BCT.GlobHecke.isHecke_globFn | (intros; apply GlobalTheory.BCT.GlobHecke.isHecke_globFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForallRealValuationLeOne
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

open IsDedekindDomain IsLocalRing

theorem exists_realValuation_of_discreteValuationSubring {Ω : Type} [Field Ω]
    (V : ValuationSubring Ω) [IsDiscreteValuationRing V] :
    ∃ ν : Valuation Ω ℝ≥0, (∀ x : V, ν (x : Ω) ≤ 1) ∧ ∀ x ∈ maximalIdeal V, ν (x : Ω) < 1 := by
  have hne : maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let v : HeightOneSpectrum V := ⟨maximalIdeal V, inferInstance, hne⟩
  let hmono := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num))
  refine ⟨(v.valuation Ω).map (WithZeroMulInt.toNNReal (e := 2) (by norm_num)) hmono.monotone,
    fun x => ?_, fun x hx => ?_⟩
  · have h := v.valuation_le_one (K := Ω) x
    have := hmono.monotone h
    simpa using this
  · have h := (v.valuation_lt_one_iff_mem (K := Ω) x).mpr hx
    have := hmono h
    simpa using this

theorem isIntegral_of_forall_realValuation_le_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  intro K Ω _ _ _ _ hfg A hA t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType K Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType A Ω := .of_comp K A Ω
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hic : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure A Ω).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := A) W
    (fun r => hW ((integralClosure A Ω).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  obtain ⟨ν, hν1, hνm⟩ := exists_realValuation_of_discreteValuationSubring V
  have hle : ν t ≤ 1 := ht ν fun a ha => hν1 ⟨a, h2 ⟨a, ha⟩⟩
  have hn3 : t⁻¹ ∈ V.nonunits := h3 _ rfl
  have htV : t⁻¹ ∈ V :=
    (V.valuation_le_one_iff _).mp (le_of_lt ((V.mem_nonunits_iff).mp hn3))
  have hm : (⟨t⁻¹, htV⟩ : V) ∈ maximalIdeal V :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨t⁻¹, htV⟩)).mp hn3
  have hlt : ν t⁻¹ < 1 := hνm _ hm
  have h1' : ν (t * t⁻¹) = 1 := by rw [mul_inv_cancel₀ ht0, map_one]
  rw [map_mul] at h1'
  have : ν t * ν t⁻¹ < 1 := lt_of_le_of_lt (mul_le_of_le_one_left zero_le hle) hlt
  exact absurd h1' this.ne

end GlobalTheory.DegVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem isKSValue_act : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (a' : OAct O A'), (∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left) → ∀ (z : O) {f : HdR A} {w : epsR R ⟶ A}, IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z) := by
  intro R _ A _ A' _ i h O _ a a' hi z f w hf
  haveI := a.hom z
  haveI := a'.hom z
  obtain ⟨k, ⟨d, hd, e⟩, l⟩ := hf
  rw [act_apply]
  have hm := push_mem_liftFil (epsDP R) h h (a.act z) (a'.act z) (e := (hi z).symm) hd
  have hl := l.push (a.act z)
  refine ⟨push (dp0 R) (𝟙 _) (a.act z) k, ⟨_, hm, fun c ↦ ?_⟩, hl⟩
  have kk := (homMor (dp0 R) (𝟙 _) (a.act z)).comp (constMor A)
  have hM := homMor (epsDP R) (DeRham.epsRed R) (a.act z)
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (a.act z)) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, e]
  rfl
end GlobalTheory.KSExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearSystemRatioOfDegreeOfGeneratesByRatios
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open GlobalTheory.DegCmp

section

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def sameDegQuot (ev : V →ₗ[K] Ω) : IntermediateField K Ω where
  carrier := {x | ∃ (e : ℕ) (q : Ω), q ∈ (LinearMap.range ev) ^ e ∧ q ≠ 0 ∧ x * q ∈ (LinearMap.range ev) ^ e}
  mul_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show x * y * (q * q') = (x * q) * (y * q') by ring]
      exact Submodule.mul_mem_mul hxq hyq'
  add_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show (x + y) * (q * q') = (x * q) * q' + q * (y * q') by ring]
      exact Submodule.add_mem _ (Submodule.mul_mem_mul hxq hq') (Submodule.mul_mem_mul hq hyq')
  algebraMap_mem' a := by
    refine ⟨0, 1, by simp [Submodule.one_eq_range], one_ne_zero, ?_⟩
    rw [pow_zero, mul_one]
    exact Submodule.algebraMap_mem a
  inv_mem' := by
    rintro x ⟨e, q, hq, hq0, hxq⟩
    by_cases hx : x = 0
    · subst hx
      exact ⟨e, q, hq, hq0, by simpa using hxq⟩
    · refine ⟨e, x * q, hxq, mul_ne_zero hx hq0, ?_⟩
      rwa [show x⁻¹ * (x * q) = q by field_simp]

theorem ratioField_le_sameDegQuot (ev : V →ₗ[K] Ω) : ratioField ev ≤ sameDegQuot ev := by
  rw [ratioField, IntermediateField.adjoin_le_iff]
  rintro a ⟨v, w, rfl⟩
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact (sameDegQuot ev).zero_mem
  · refine ⟨1, ev w, by simp, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]
    exact LinearMap.mem_range_self ev v

theorem isRatio_of_genRatios (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) : GenRatios ev → ∀ (τ : ℕ) (t : Ω), IsRatio ev τ t := by
  rintro ⟨hev, htop⟩ τ t
  obtain ⟨w, hw⟩ : ∃ w, ev w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hev (LinearMap.ext h)
  have hmem : t / ev w ^ τ ∈ sameDegQuot ev := by
    apply ratioField_le_sameDegQuot ev
    rw [htop]; trivial
  obtain ⟨e, q, hq, hq0, hp⟩ := hmem
  refine ⟨e, q, hq, hq0, ?_⟩
  have : t * q = (t / ev w ^ τ * q) * ev w ^ τ := by
    field_simp
  rw [this, add_comm, pow_add]
  exact Submodule.mul_mem_mul hp (Submodule.pow_mem_pow _ (LinearMap.mem_range_self ev w) τ)

end

end GlobalTheory.DegVal
end
end

