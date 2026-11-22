import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0006
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0004

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IntMatIsCompact
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

theorem intMat_isOpen (m n : ℕ) :
    IsOpen {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} := by
  have e : {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} =
      ⋂ i, ⋂ j, (fun w : Matrix (Fin m) (Fin n) (AfE D) => w i j) ⁻¹' (intAE D : Set (AfE D)) := by
    ext w; simp
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))

theorem intMat_isCompact (m n : ℕ) :
    IsCompact {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D} :=
  isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D

theorem U_isOpen {S : Finset (Pl D)} {ef : AfE D} (hef : ef ∈ intAE D) (N m n : ℕ) :
    IsOpen (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  refine AddSubgroup.isOpen_of_mem_nhds (U S ef N m n) (g := 0) ?_
  refine Filter.mem_of_superset ((intMat_isOpen m n).mem_nhds fun i j => zero_mem _) fun w hw => ?_
  exact ⟨fun v _ i j => cf_mem_of_mem (hw i j) v, fun i j =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N)
      (GlobalTheory.HostAdeleIso.intAE_mul_mem D hef (hw i j))⟩

open Classical in
theorem U_isCompact {S : Finset (Pl D)} {ef : AfE D} (hef : ef ∈ intAE D)
    (hS : ∀ v : Pl D, cf v ef = if v ∈ S then 1 else 0) {N : ℕ} (hN : 0 < N) (m n : ℕ) :
    IsCompact (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hcl : IsClosed (U S ef N m n : Set (Matrix (Fin m) (Fin n) (AfE D))) :=
    AddSubgroup.isClosed_of_isOpen _ (U_isOpen hef N m n)
  let c : AfE D := algebraMap D.host.F (AfE D) ((N : D.host.F)⁻¹)
  have hc : c * (N : AfE D) = 1 := by
    have hN' : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← map_natCast (algebraMap D.host.F (AfE D)) N, ← map_mul, inv_mul_cancel₀ hN', map_one]
  have hK : IsCompact ((fun w : Matrix (Fin m) (Fin n) (AfE D) => Matrix.of fun i j => c * w i j) ''
      {w : Matrix (Fin m) (Fin n) (AfE D) | ∀ i j, w i j ∈ intAE D}) :=
    (intMat_isCompact m n).image (continuous_pi fun i => continuous_pi fun j =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  refine hK.of_isClosed_subset hcl fun w hw => ?_
  refine ⟨Matrix.of fun i j => (N : AfE D) * w i j, fun i j => ?_, ?_⟩
  · have h1 : (1 - ef) * w i j ∈ intAE D := mem_of_cf_mem fun v => by
      rw [map_mul, map_sub, map_one, hS v]
      by_cases hv : v ∈ S
      · rw [if_pos hv, sub_self, zero_mul]; exact zero_mem _
      · rw [if_neg hv, sub_zero, one_mul]; exact hw.1 v hv i j
    have h2 : (N : AfE D) * w i j = (N : AfE D) * (ef * w i j) + (N : AfE D) * ((1 - ef) * w i j) := by ring
    rw [Matrix.of_apply, h2]
    exact add_mem (hw.2 i j) (GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE N) h1)
  · ext i j
    simp only [Matrix.of_apply]
    rw [← mul_assoc, hc, one_mul]

end PositivityTheory.Rg.Rsw.L.LBumpEx

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKD
section
noncomputable section

open scoped TensorProduct NNReal
open Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_fromBlocks {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R) :
    cj s (fromBlocks a b c d) = fromBlocks (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold cj
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cj_neg {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) : cj s (-M) = -cj s M := by
  ext i j; simp [cj]

theorem cj_zero {R : Type} [CommRing R] (s : R →+* R) {m p : Type} : cj s (0 : Matrix m p R) = 0 := by
  ext i j; simp [cj]

theorem unit_rel {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    a * cj s d - b * cj s c = 1 ∧ c * cj s d = d * cj s c ∧ d * cj s a - c * cj s b = 1 := by
  set M := fromBlocks a b c d with hM
  set J : Matrix (n ⊕ n) (n ⊕ n) R := fromBlocks 0 1 (-1) 0 with hJ
  have hJJ : J * J = -1 := by
    rw [hJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have h1 : (-(J * cj s M * J)) * M = 1 := by
    calc (-(J * cj s M * J)) * M = -(J * (cj s M * J * M)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJJ, neg_neg]
  have h2 : M * (-(J * cj s M * J)) = 1 := mul_eq_one_comm.mp h1
  have e : M * J * cj s M * J = -1 := by
    rw [Matrix.mul_neg] at h2
    simp only [Matrix.mul_assoc] at h2 ⊢
    exact neg_eq_iff_eq_neg.mp h2
  have h3 : M * J * cj s M = J := by
    calc M * J * cj s M = -(M * J * cj s M * (J * J)) := by rw [hJJ]; simp
      _ = -(M * J * cj s M * J * J) := by simp [Matrix.mul_assoc]
      _ = J := by rw [e]; simp
  rw [hM, hJ, cj_fromBlocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  simp at h3
  obtain ⟨-, k1, k2, k3⟩ := h3
  rw [neg_add_eq_sub] at k1 k2 k3
  refine ⟨k1, sub_eq_zero.mp k3, ?_⟩
  rw [← neg_sub, k2, neg_neg]

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem local_choice (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ AlgHom.id F E)
    (hfr : Module.finrank F E = 2) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (a b c d : Matrix n n (Fv F v ⊗[F] E))
    (ha : ∀ i j, a i j ∈ intLoc F E v) (hb : ∀ i j, b i j ∈ intLoc F E v) (hc : ∀ i j, c i j ∈ intLoc F E v)
    (hd : ∀ i j, d i j ∈ intLoc F E v)
    (hu : cj (sigR (Fv F v) σ) (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d =
      fromBlocks 0 1 (-1) 0) :
    ∃ x : Matrix n n (Fv F v ⊗[F] E), (∀ i j, x i j ∈ intLoc F E v) ∧ cj (sigR (Fv F v) σ) x = x ∧
      ∃ z ∈ intLoc F E v, (d + c * x).det * z = 1 := by
  have hinv : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => simp [sigR, hσ]
    | add p q hp hq => simp only [map_add, hp, hq]
  set s := sR v σ with hs
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply Subtype.ext
    rw [hs, coe_sR, coe_sR, hinv]
  have hπ : ∀ y, (intLoc F E v).subtype (s y) = sigR (Fv F v) σ ((intLoc F E v).subtype y) := by
    intro y
    exact coe_sR v σ y
  let a' : Matrix n n (intLoc F E v) := fun i j => ⟨a i j, ha i j⟩
  let b' : Matrix n n (intLoc F E v) := fun i j => ⟨b i j, hb i j⟩
  let c' : Matrix n n (intLoc F E v) := fun i j => ⟨c i j, hc i j⟩
  let d' : Matrix n n (intLoc F E v) := fun i j => ⟨d i j, hd i j⟩
  have ea : a'.map (intLoc F E v).subtype = a := rfl
  have eb : b'.map (intLoc F E v).subtype = b := rfl
  have ec : c'.map (intLoc F E v).subtype = c := rfl
  have ed : d'.map (intLoc F E v).subtype = d := rfl
  have h1m : (1 : Matrix n n (intLoc F E v)).map (intLoc F E v).subtype = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hJm : (fromBlocks 0 1 (-1) 0 : Matrix (n ⊕ n) (n ⊕ n) (intLoc F E v)).map (intLoc F E v).subtype
      = fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg (intLoc F E v).subtype), h1m]
    simp
  have hu' : cj s (fromBlocks a' b' c' d') * fromBlocks 0 1 (-1) 0 * fromBlocks a' b' c' d' =
      fromBlocks 0 1 (-1) 0 := by
    apply Matrix.map_injective Subtype.val_injective
    have key := hu
    rw [← ea, ← eb, ← ec, ← ed, ← Matrix.fromBlocks_map, ← map_cj s _ _ hπ, ← hJm,
      ← Matrix.map_mul, ← Matrix.map_mul] at key
    exact key
  obtain ⟨k1, k2, k3⟩ := unit_rel s a' b' c' d' hu'
  obtain ⟨𝔭, h𝔭, hloc⟩ := exists_max v σ hσ1 hfr
  obtain ⟨B, hB, hdet⟩ := core s hss 𝔭 (isUnit_two v h2) hloc a' b' c' d' k1 k2 k3
  obtain ⟨w, hw⟩ := hdet.exists_right_inv
  refine ⟨B.map (intLoc F E v).subtype, fun i j => (B i j).2, ?_, w, w.2, ?_⟩
  · rw [← map_cj s _ _ hπ, hB]
  · have hm : (d' + c' * B).map (intLoc F E v).subtype = d + c * B.map (intLoc F E v).subtype := by
      rw [Matrix.map_add _ (map_add (intLoc F E v).subtype), Matrix.map_mul, ec, ed]
    rw [← hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using congrArg Subtype.val hw

end Local

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvB
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

variable {D : D7}

open Classical in

theorem exists_int_off {K : Set (Af D.host.F)} (hK : IsCompact K) :
    ∃ T : Finset (Pl D), ∀ z ∈ K, ∀ v ∉ T, z v ∈ v.adicCompletionIntegers D.host.F := by
  classical
  let O : Finset (Pl D) → Set (Af D.host.F) :=
    fun T => {z | ∀ v, v ∉ T → z v ∈ (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))}
  have hO : ∀ T, IsOpen (O T) := fun T =>
    RestrictedProduct.isOpen_forall_imp_mem (R := fun v : Pl D => v.adicCompletion D.host.F)
      (A := fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have hcov : K ⊆ ⋃ T, O T := fun z _ => Set.mem_iUnion.2
    ⟨(Filter.eventually_cofinite.1 z.2).toFinset, fun v hv => by
      by_contra h
      exact hv ((Filter.eventually_cofinite.1 z.2).mem_toFinset.2 h)⟩
  obtain ⟨T, hT⟩ := hK.elim_directed_cover O hO hcov fun T T' =>
    ⟨T ∪ T', fun z hz v hv => hz v fun h => hv (Finset.mem_union_left _ h),
      fun z hz v hv => hz v fun h => hv (Finset.mem_union_right _ h)⟩
  exact ⟨T, fun z hz v hv => hT hz v hv⟩

def sPart {a b : ℕ} (S : Finset (Pl D)) (y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i j => algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) * y i j

open Classical in
set_option maxHeartbeats 800000 in

theorem fin_good {a b : ℕ} (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ y, g y =
      if (∀ v ∉ S, ∀ i j, projV v y i j ∈ intLoc D.host.F D.host.E v)
      then g (sPart S y) else 0 := by
  classical
  obtain ⟨hlc, hcs⟩ := hg
  let B := Module.finBasis D.host.F D.host.E
  have hT1 : ∀ (i : Fin a) (j : Fin b) (k : Fin (Module.finrank D.host.F D.host.E)), ∃ T : Finset (Pl D),
      ∀ y ∈ tsupport g, ∀ v ∉ T, crd B (Af D.host.F) (y i j) k v ∈ v.adicCompletionIntegers D.host.F := by
    intro i j k
    have hc : Continuous fun y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E => y i j :=
      (continuous_apply j).comp (continuous_apply i)
    obtain ⟨T, hT⟩ := exists_int_off (D := D) (hcs.isCompact.image ((continuous_crd B (Af D.host.F) k).comp hc))
    exact ⟨T, fun y hy v hv => hT _ ⟨y, hy, rfl⟩ v hv⟩
  choose T1 hT1 using hT1
  have hU := invariant_mem_nhds hlc hcs
  let Lc : (Fin a → Fin b → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) →
      (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af D.host.F) ⊗ₜ[D.host.F] B k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af D.host.F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T2, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  have hinv : ∀ x u, (∀ i j k v, crd B (Af D.host.F) (u i j) k v ∈ P v) → g (x + u) = g x := by
    intro x u hu
    have hu' : u = Lc fun i j k => crd B (Af D.host.F) (u i j) k := by
      funext i j
      exact eq_sum_crd B (Af D.host.F) (u i j)
    rw [hu']
    exact h1 _ (fun i => h2 _ fun j => h3 _ fun k => hsub (hu i j k)) x
  have hbad := Filter.eventually_cofinite.1 (GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr B)
  refine ⟨(Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => Finset.univ.biUnion fun k => T1 i j k) ∪ T2 ∪
    hbad.toFinset, fun S hS y => ?_⟩
  have hS1 : ∀ i j k, T1 i j k ⊆ S := fun i j k v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hv⟩⟩⟩)))
  have hS2 : T2 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hS3 : ∀ v ∉ S, ∀ z : Fv D.host.F v ⊗[D.host.F] D.host.E, z ∈ intLoc D.host.F D.host.E v ↔
      ∀ k, crd B (Fv D.host.F v) z k ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    have h' : v ∉ hbad.toFinset := fun h => hv (hS (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h'
    exact h'
  have hcrd : ∀ z k, crd B (Af D.host.F) (z - algebraMap (Af D.host.F) _ (indS S) * z) k =
      crd B (Af D.host.F) z k - indS S * crd B (Af D.host.F) z k := by
    intro z k
    simp only [crd, ← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  split_ifs with h
  · calc g y = g (sPart S y + (y - sPart S y)) := by rw [add_sub_cancel]
      _ = g (sPart S y) := hinv _ _ fun i j k v => ?_
    have e1 : crd B (Af D.host.F) ((y - sPart S y) i j) k v =
        crd B (Af D.host.F) (y i j) k v - indS S v * crd B (Af D.host.F) (y i j) k v := by
      rw [Pi.sub_apply, Pi.sub_apply, sPart, hcrd]
      rfl
    rw [e1, indS_apply]
    by_cases hv : v ∈ S
    · rw [if_pos hv, one_mul, sub_self]
      exact zero_mem _
    · rw [if_neg hv, zero_mul, sub_zero, hPT v fun h' => hv (hS2 h'), mem_intSub, ← crd_projV]
      exact (hS3 v hv _).1 (h v hv i j) k
  · push Not at h
    obtain ⟨v, hv, i, j, hij⟩ := h
    obtain ⟨k, hk⟩ : ∃ k, crd B (Fv D.host.F v) (projV v y i j) k ∉ v.adicCompletionIntegers D.host.F := by
      by_contra hc
      push Not at hc
      exact hij ((hS3 v hv _).2 hc)
    rw [crd_projV] at hk
    refine image_eq_zero_of_notMem_tsupport fun hy => hk ?_
    exact hT1 i j k y hy v fun h' => hv (hS1 i j k h')

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MulVecInt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {D : D7} {n : ℕ}

theorem mat_proj (v : Pl D) (g : G D n) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :
      Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = (mat g).map (cv D v) := rfl

theorem mulVec_int (v : Pl D) {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv D.host.F v ⊗[D.host.F] D.host.E))
    (x : Fin m → Fv D.host.F v ⊗[D.host.F] D.host.E) (hA : ∀ i j, A i j ∈ intLoc D.host.F D.host.E v)
    (hx : ∀ j, x j ∈ intLoc D.host.F D.host.E v) (i : Fin m) : (A *ᵥ x) i ∈ intLoc D.host.F D.host.E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hA i j) (hx j)

theorem single_int (v : Pl D) {m : ℕ} (j : Fin m) (i : Fin m) :
    (Pi.single j (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) : Fin m → _) i ∈ intLoc D.host.F D.host.E v := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem KOff_props {D : D7} {n : ℕ} {S : Finset (Pl D)} {k : G D n} (hk : k ∈ KOff D n S) :
    (mat k).map (infPart D) = 1 ∧ (∀ v ∈ S, (mat k).map (cv D v) = 1) ∧
    ∀ v ∉ S, ∀ i j, cv D v (mat k i j) ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨⟨hfin, haway⟩, hoff⟩ := Subgroup.mem_inf.1 hk
  refine ⟨congrArg Units.val (MonoidHom.mem_ker.1 hfin), fun v hv => ?_, fun v hv i j => ?_⟩
  · have h1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 haway v) hv)
    rw [← mat_proj, h1, map_one, Units.val_one]
  · have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hoff v) hv)
    have h2 := Subgroup.mem_comap.1 h1
    have hs : (Pi.single j 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
        latLoc D.host.F (stdLattice D.host.E (n + n)) v :=
      mem_latLoc_stdLattice.2 (single_int v j)
    have h3 := mem_latLoc_stdLattice.1 ((h2 _).1 hs) i
    rw [mat_proj] at h3
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

theorem mem_KOff {D : D7} {n : ℕ} {S : Finset (Pl D)} (g : G D n) (hinf : (mat g).map (infPart D) = 1)
    (hS : ∀ v ∈ S, (mat g).map (cv D v) = 1)
    (hint : ∀ v ∉ S, ∀ i j, cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧
      cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v) :
    g ∈ KOff D n S := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (Units.ext hinf), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => MonoidHom.mem_ker.2 ?_
    refine matHom_injective _ _ _ (Units.ext ?_)
    rw [mat_proj, hS v hv, map_one, Units.val_one]
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_comap.2 ?_)
    have hM : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).1
    have hM' : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).2
    have hinv : ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *
        ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Units.val_one]
    intro x
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
    constructor
    · intro hx i
      exact mulVec_int v _ x hM hx i
    · intro hx i
      have e : x = ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ
          (((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [e]
      exact mulVec_int v _ _ hM' hx i

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.NatCastMulGen
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixW.U2

variable {D : D7}

theorem norm_mem {v : Pl D} (hv : IsGood D.host.F D.host.E v) {x : Fv D.host.F v ⊗[D.host.F] D.host.E}
    (hx : x ∈ intLoc D.host.F D.host.E v) :
    Algebra.norm (Fv D.host.F v) x ∈ v.adicCompletionIntegers D.host.F := by
  classical
  rw [Algebra.norm_eq_matrix_det (bV (E := D.host.E) v), Matrix.det_apply]
  have hM : ∀ i j, Algebra.leftMulMatrix (bV (E := D.host.E) v) x i j ∈ v.adicCompletionIntegers D.host.F := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hb : bV (E := D.host.E) v j ∈ intLoc D.host.F D.host.E v := by
      rw [bV_apply]; exact one_tmul_b_mem hv j
    exact (mem_intLoc_iff hv _).1 (mul_mem hx hb) i
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

theorem absEv_eq_one {v : Pl D} (hv : IsGood D.host.F D.host.E v) (x : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (h1 : (x : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v)
    (h2 : ((x⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v) :
    absEv D.host.F D.host.E v x = 1 := by
  have k : ∀ y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v → absEv D.host.F D.host.E v y ≤ 1 := fun y hy => by
    rw [absEv_apply]
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (norm_mem hv hy)
  have a1 := k x h1
  have a2 := k _ h2
  have hm : absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ≥0) = absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ := hm.symm
    _ ≤ absEv D.host.F D.host.E v x * 1 := mul_le_mul_of_nonneg_left a2 (by positivity)
    _ = absEv D.host.F D.host.E v x := mul_one _

def cN (D : D7) (N : ℕ) : AE D := algebraMap D.host.F (AF D.host.F) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cv_cN (v : Pl D) (N : ℕ) :
    cv D v (cN D N) = algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  show evFin D.host.F v (algebraMap D.host.F (AF D.host.F) _) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [AlgHom.commutes]

theorem natCast_mul_gen {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] {N : ℕ}
    (hN : (N : F) ≠ 0) : (N : A ⊗[F] E) * (algebraMap F A ((N : F)⁻¹) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [(map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := A) (B := E)) N).symm]
  show ((N : A) ⊗ₜ[F] (1 : E)) * _ = 1
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_natCast (algebraMap F A) N, ← map_mul,
    mul_inv_cancel₀ hN, map_one]
  rfl

theorem natCast_mul_cN {N : ℕ} (hN : 0 < N) : (N : AE D) * cN D N = 1 :=
  natCast_mul_gen (by exact_mod_cast hN.ne')

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end

