import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PointVertical

section Reduction

variable {K : Type} {ι : K → Type} (p : ℕ)

abbrev red : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)

theorem ker_red_le {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    RingHom.ker (red (ι := ι) p) ≤ J := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  simpa using hp

theorem mem_map_red_iff {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp

theorem ringKrullDim_red {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    ringKrullDim (MRingOver (ZMod p) ι ⧸ J.map (red p)) = ringKrullDim (MRing ι ⧸ J) := by
  have e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p)) := by
    ext g
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm

theorem isMultiProjPrime_red [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)} (hJ : IsMultiProjPrime J)
    (hp : ((p : ℕ) : MRing ι) ∈ J) : IsMultiProjPrime (J.map (red p)) := by
  obtain ⟨hJp, ⟨S, hS, hJS⟩, hJr⟩ := hJ
  refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp),
    ⟨red p '' S, ?_, by rw [hJS, Ideal.map_span]⟩, fun k => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩
  · obtain ⟨i, hi⟩ := hJr k
    refine ⟨i, fun h => hi ((mem_map_red_iff p hp _).mp ?_)⟩
    rw [map_X]
    exact h

variable {K' : Type} {ι' : K' → Type}

theorem imageVar_red [Fact p.Prime] (v : (Σ k, ι k) → (Σ k', ι' k')) {W : Ideal (MRing ι')}
    (hp : ((p : ℕ) : MRing ι') ∈ W) :
    imageVar (ZMod p) v (W.map (red p)) = (imageZ v W).map (red p) := by
  have hp' : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hp
  ext f
  obtain ⟨g, rfl⟩ := red_surjective p f
  rw [mem_map_red_iff p hp' g]
  show rename v (red p g) ∈ W.map (red p) ↔ rename v g ∈ W
  rw [← map_rename, mem_map_red_iff p hp]

theorem isMultiHomog_rename [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRing ι} {a : K → ℕ} (ht : IsMultiHomog t a) :
    IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem isMultiProjPrime_imageZ [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRing ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageZ v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := ℤ) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

end Reduction

theorem exists_dim_F {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) [Fact p.Prime]
    (V : Ideal (MRingOver (ZMod p) ι)) (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver (ZMod p) ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem geoNum_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d n : ℕ}
    (hP : IsArithVar (imageZ v P') d) (hdn : d < n + 1) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((n + Fintype.card K' : ℕ) : WithBot ℕ∞)) (L : Fin n → K → ℤ) :
    geoNum n W (fun j => pullDeg κ (L j)) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) n := ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  obtain ⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩ := hP
  have := hQp
  have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
  have hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P' := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact h
    rw [hQh, Ideal.mem_bot] at h2
    exact hpr.ne_zero (by exact_mod_cast h2)
  have hdim := krullDim_quot_add_one_le hle hpI hpQ
  rw [← ringKrullDim_red p hpI, hD, hQd] at hdim
  have hD' : D + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K' ι'
  rw [hGeo K' ι' p I hI W n _ hWm hpW hWp]
  exact hPC (ZMod p) K ι K' ι' I hI κ v _ n _ L hv hWp hVi (by omega)

end PointVertical

open PointVertical in

theorem ProjectivePointVertical.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι') :
    ProjectivePointVertical.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d n L L' t a hv hP' hP hdn hL ht htQ
  classical
  have hs : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ a 0)) (rename v t) :=
    ⟨Function.extend κ a 0, fun _ => rfl, isMultiHomog_rename hv ht, htQ⟩
  unfold vertR
  refine finsum_mem_eq_zero_of_forall_eq_zero fun W hW => ?_
  obtain ⟨-, hvert⟩ := divSuppArith K' ι' P' n _ _ W hP' hs hW
  by_cases hh : IsHorizontal W
  · simp [hh]
  · obtain ⟨hWm, hpr, hWd⟩ := hvert hh
    have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
    have e : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hL j).1
    simp only [if_neg hh, e, geoNum_eq_zero hGeo hR4 hPC hv hP hdn hPW hWm hpr hWd (fun j => (L j).a)]
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.OrderOfIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem RegularityOrder.order_of_integral {F : Type*} [Field F] [NumberField F] (S : Subring F)
    (hint : ∀ x ∈ S, IsIntegral ℤ x) (hden : ∀ x : F, ∃ c ∈ S, c ≠ 0 ∧ x * c ∈ S) :
    Module.Finite ℤ S ∧ Module.Free ℤ S ∧ Module.finrank ℤ S = Module.finrank ℚ F := by

  have hmul : ∀ x : F, ∃ m : ℤ, m ≠ 0 ∧ (m : F) * x ∈ S := by
    intro x
    obtain ⟨c, hc, hc0, hxc⟩ := hden x
    have hci : IsIntegral ℤ (⟨c, hc⟩ : S) :=
      (isIntegral_algHom_iff S.subtype.toIntAlgHom Subtype.val_injective).1 (hint c hc)
    have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hc⟩ : S)})
      (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hm)
    refine ⟨m, hm0, ?_⟩
    have hmdc : (m : F) = (d : F) * c := by
      have := congrArg Subtype.val hd
      simpa using this.symm
    rw [hmdc, mul_assoc, mul_comm c x]
    exact S.mul_mem d.2 hxc

  let φ : S →ₗ[ℤ] 𝓞 F :=
    { toFun := fun x => ⟨x, hint x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext (congrArg (fun z : 𝓞 F => (z : F)) h)
  have : Module.Finite ℤ S := Module.Finite.of_injective φ hφ
  have : Module.IsTorsionFree ℤ S := hφ.moduleIsTorsionFree φ (fun r x => φ.map_smul r x)
  have : Module.Free ℤ S := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, inferInstance, le_antisymm ?_ ?_⟩
  · rw [← RingOfIntegers.rank]
    exact LinearMap.finrank_le_finrank_of_injective hφ
  · rw [← RingOfIntegers.rank]
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 F)
    choose m hm0 hmS using fun i => hmul (s i : F)
    have hM0 : (∏ i, m i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hm0 i
    have hMS : ∀ y : 𝓞 F, ((∏ i, m i : ℤ) : F) * y ∈ S := by
      intro y
      have hy : y ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        obtain ⟨q, hq⟩ : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
        rw [hq, Int.cast_mul, mul_comm (m i : F), mul_assoc]
        exact S.mul_mem (intCast_mem S q) (hmS i)
      | zero => simp
      | add y z _ _ hy hz =>
        convert S.add_mem hy hz using 1
        push_cast
        ring
      | smul r y _ hy =>
        convert S.zsmul_mem hy r using 1
        simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast]
        ring
    let ψ : 𝓞 F →ₗ[ℤ] S :=
      { toFun := fun y => ⟨((∏ i, m i : ℤ) : F) * y, hMS y⟩
        map_add' := fun y z => Subtype.ext (by push_cast; ring)
        map_smul' := fun r y => Subtype.ext (by
          simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast,
            Subring.coe_mul, SubringClass.coe_intCast, RingHom.id_apply]
          ring) }
    have hψ : Function.Injective ψ := by
      intro y z h
      have h' : ((∏ i, m i : ℤ) : F) * y = ((∏ i, m i : ℤ) : F) * z := congrArg Subtype.val h
      exact RingOfIntegers.eq_iff.1 (mul_left_cancel₀ (Int.cast_ne_zero.2 hM0) h')
    exact LinearMap.finrank_le_finrank_of_injective hψ

theorem RegularityOrder.proof (h₁ : RegularityFunctionFieldNumber.Statement) (h₂ : RegularityDenominator.Statement)
    (h₃ : RegularityIntegral.Statement) : RegularityOrder.Statement := by
  intro K _ ι _ P hP
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun r => by simp }
  have hint₀ : ∀ x ∈ regRing P, IsIntegral ℤ x := fun x hx =>
    (isIntegral_algHom_iff f Subtype.val_injective).1 (h₃ K ι P hP ⟨x, hx⟩)
  obtain ⟨hF, hN⟩ := h₁ K ι P hP
  let _ : Field (funField P) := hF.toField
  have := hN
  have hint : ∀ x ∈ regRing P, IsIntegral ℤ x := hint₀
  have hden : ∀ x : funField P, ∃ c ∈ regRing P, c ≠ 0 ∧ x * c ∈ regRing P := by
    intro x
    obtain ⟨c, hc0, hc⟩ := h₂ K ι P x hP
    exact ⟨c, fun W h1 h2 => (hc W h1 h2).1, hc0, fun W h1 h2 => (hc W h1 h2).2⟩
  obtain ⟨hfin, hfree, hrank⟩ := RegularityOrder.order_of_integral (F := funField P) (regRing P) hint hden
  exact ⟨hfree, hfin, fun _ _ => hrank⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagArith
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem exists_minor_ne_zero {F : Type} [Field F] {r N : ℕ} (M : Matrix (Fin r) (Fin N) F)
    (hM : LinearIndependent F M.row) :
    ∃ (S : Finset (Fin N)) (hS : S.card = r), (M.submatrix id (S.orderEmbOfFin hS)).det ≠ 0 := by
  classical
  obtain ⟨b, -, -, hsp, hb⟩ := exists_linearIndepOn_extension (K := F) (v := M.col)
    (linearIndepOn_empty F M.col) (Set.empty_subset Set.univ)
  have h1 : Submodule.span F (M.col '' b) = Submodule.span F (Set.range M.col) := by
    refine le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact hsp ⟨i, Set.mem_univ _, rfl⟩
  have h2 : Module.finrank F (Submodule.span F (M.col '' b)) = Fintype.card b := by
    rw [Set.image_eq_range]
    exact finrank_span_eq_card hb
  rw [h1, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin] at h2
  have hS : b.toFinset.card = r := by rw [Set.toFinset_card]; exact h2.symm
  refine ⟨b.toFinset, hS, ?_⟩
  have hmem : ∀ c, b.toFinset.orderEmbOfFin hS c ∈ b := fun c =>
    Set.mem_toFinset.1 (b.toFinset.orderEmbOfFin_mem hS c)
  have hli : LinearIndependent F (M.submatrix id (b.toFinset.orderEmbOfFin hS)).col :=
    hb.comp (fun c => ⟨_, hmem c⟩) fun c c' h => by
      have h' := congrArg Subtype.val h
      exact (b.toFinset.orderEmbOfFin hS).injective h'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero

section Flag

variable {K : Type} {ι : K → Type}

theorem flagMap_X_inr (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    flagMap P B (X (⟨Sum.inr j, S⟩ : Σ k, FlagBundleBlocks ι N1 n k)) =
      flagMinor (genMat (FnField P) n * B.map C) j S := by
  simp [flagMap]

theorem eval_one_flagMinor (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    eval (fun q : Fin n × Fin n => if q.1 = q.2 then (1 : FnField P) else 0)
      (flagMinor (genMat (FnField P) n * B.map C) j S) = flagMinor B j S := by
  rw [flagMinor, flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.submatrix_apply]
  erw [Matrix.mul_apply]
  simp [genMat]

theorem exists_X_inr_notMem (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B)
    (j : Fin (n - 1)) : ∃ S : PluckerBlocks N1 n j, (X (⟨Sum.inr j, S⟩ : Σ k, FlagBundleBlocks ι N1 n k)) ∉ flagIdeal P B := by
  have hj : (j : ℕ) + 1 ≤ n := by have := j.2; omega
  obtain ⟨S, hS, hne⟩ := exists_minor_ne_zero (B.submatrix (Fin.castLE hj) id)
    (hB.comp _ (Fin.castLE_injective hj))
  refine ⟨⟨S, hS⟩, fun h => hne ?_⟩
  rw [flagIdeal, RingHom.mem_ker, flagMap_X_inr] at h
  have := eval_one_flagMinor P B j ⟨S, hS⟩
  rw [h, map_zero] at this
  exact this.symm

theorem algebraMap_int_injective (I : Ideal (MRing ι)) (h : IsHorizontal I) :
    Function.Injective (algebraMap ℤ (MRing ι ⧸ I)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at ha
  have h' : a ∈ I.comap (C : ℤ →+* MRing ι) := ha
  rw [show I.comap (C : ℤ →+* MRing ι) = ⊥ from h] at h'
  exact (Submodule.mem_bot ℤ).mp h'

end Flag

theorem FlagArith.proof (hMH : FlagMultiHomog.Statement) (hTr : FlagConeTrdeg.Statement)
    (hDim : IntDomainDim.Statement) : FlagArith.Statement := by
  intro K _ ι _ N1 t n P d c m B hP hc hB
  have := hP.2.1.1

  have hHor : IsHorizontal (flagIdeal P B) := by
    have h := hP.2.2.1
    rw [← imageZ_flagIdeal P B] at h
    refine Eq.trans (Ideal.ext fun a => ?_) h
    simp only [Ideal.mem_comap, imageZ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
  have hprime : (flagIdeal P B).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨Sum.inl hP.1.some⟩, ⟨hprime, hMH K ι N1 t n P c m B hP.2.1.1 hP.2.1.2.1 hc.1 hB, ?_⟩, hHor, ?_⟩
  ·
    rintro (k | j)
    · obtain ⟨i, hi⟩ := hP.2.1.2.2 k
      refine ⟨i, fun h => hi ?_⟩
      rw [← imageZ_flagIdeal P B]
      show rename inlV (X ⟨k, i⟩) ∈ flagIdeal P B
      rwa [rename_X]
    · obtain ⟨S, hS⟩ := exists_X_inr_notMem P B hB.1 j
      exact ⟨S, hS⟩
  ·
    have dimP := hDim (MRing ι ⧸ P) (algebraMap_int_injective P hP.2.2.1)
    have dimF := hDim (MRing (FlagBundleBlocks ι N1 n) ⧸ flagIdeal P B) (algebraMap_int_injective _ hHor)
    rw [hTr K ι N1 n P B hP.2.1.1 hP.2.2.1 hB.1] at dimF
    rw [hP.2.2.2] at dimP
    rw [dimF]
    have hK : 0 < Fintype.card K := Fintype.card_pos_iff.2 hP.1
    have h1 : ((d + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1 := by
      exact_mod_cast dimP
    simp only [map_add, map_natCast, Fintype.card_sum, Fintype.card_fin]
    generalize (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = s at h1 ⊢
    induction s using ENat.recTopCoe with
    | top => simp at h1
    | coe s =>
      norm_cast at h1 ⊢
      rw [show s + (flagDim n + (n - 1)) + 1 = flagDim n + d + (Fintype.card K + (n - 1)) by omega]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagConeTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_flagMap_X (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    ((aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) :
      MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P)) = flagMap P B :=
  MvPolynomial.ringHom_ext (fun r => by
    rw [← RingHom.comp_apply _ C r, ← RingHom.comp_apply _ C r, eq_intCast, eq_intCast]) fun q => by
    simp

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem range_aeval_flagMap_X (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range =
      Algebra.adjoin ℤ
        (Set.range (fun d : MRing ι ⧸ P => algebraMap (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))
            (algebraMap (MRing ι ⧸ P) (FnField P) d)) ∪
          Set.range fun q : Σ j, PluckerBlocks N1 n j => flagMinor (genMat (FnField P) n * B.map C) q.1 q.2) := by
  rw [← Algebra.adjoin_range_eq_range_aeval]
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k | j, i⟩, rfl⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨Ideal.Quotient.mk P (X ⟨k, i⟩), by simp [flagMap, genPt, algebraMap_eq]⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨⟨j, i⟩, by simp [flagMap]⟩)
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨d, rfl⟩ | ⟨⟨j, S⟩, rfl⟩)
    · obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
      have e := @aeval_comp_X _ _ _ _ _ inferInstance (Ideal.Quotient.mk P)
        ((algebraMap (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))).comp
          (algebraMap (MRing ι ⧸ P) (FnField P))) f
      have hm : aeval (fun p => flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p))) f ∈
          Algebra.adjoin ℤ (Set.range fun p => flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p))) := by
        rw [Algebra.adjoin_range_eq_range_aeval]
        exact ⟨f, rfl⟩
      simp_rw [flagMap_X_inl] at hm
      refine Algebra.adjoin_mono ?_ (e ▸ hm)
      · rintro _ ⟨p, rfl⟩
        exact ⟨_, flagMap_X_inl P B p⟩
    · exact Algebra.subset_adjoin ⟨⟨Sum.inr j, S⟩, by simp [flagMap]⟩

theorem FlagConeTrdeg.proof (h₁ : TrdegAdjoinFrac.Statement) (h₂ : FlagMinorsBaseChange.Statement)
    (h₃ : FlagMinorsTrdeg.Statement) : FlagConeTrdeg.Statement := by
  intro K _ ι _ N1 n P B hP hH hB
  have hinj : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : C a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [Ideal.Quotient.algebraMap_eq, algebraMap_eq] using ha
    have h2 : a ∈ P.comap (C : ℤ →+* MRing ι) := this
    rwa [hH, Ideal.mem_bot] at h2
  have e := Ideal.quotientKerEquivRange
    (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))
  have hk : RingHom.ker
      (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) =
        flagIdeal P B := by
    ext f
    have h : ((aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) :
          MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P)) f = flagMap P B f := by
      rw [aeval_flagMap_X]
    rw [RingHom.mem_ker, flagIdeal, RingHom.mem_ker, ← h, RingHom.coe_coe]
  have ht : Algebra.trdeg ℤ (MRing (FlagBundleBlocks ι N1 n) ⧸ RingHom.ker
      (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))) =
      Algebra.trdeg ℤ (aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range := by
    have e' : (MRing (FlagBundleBlocks ι N1 n) ⧸ RingHom.ker (aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))) ≃ₐ[ℤ]
        (aeval fun q => flagMap P B (X q) :
          MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range := e
    exact e'.trdeg_eq
  have e2 := h₂ (FnField P) n N1 B hB
  rw [← hk, ht, range_aeval_flagMap_X]
  exact (h₁ (MRing ι ⧸ P) (MvPolynomial (Fin n × Fin n) (FnField P)) _ hinj).trans (by rw [e2, h₃])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

