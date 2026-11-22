import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0562
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
section
open Formalism.L2.Col

namespace GlobalTheory.ScalarExtEig

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
  {σ : K →+* ℂ} (j : V →ₛₗ[σ] W)

theorem span_image_span (S : Set V) :
    Submodule.span ℂ (j '' (Submodule.span K S : Set V)) = Submodule.span ℂ (j '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem span_image_mono {U U' : Submodule K V} (h : U ≤ U') :
    Submodule.span ℂ (j '' (U : Set V)) ≤ Submodule.span ℂ (j '' (U' : Set V)) :=
  Submodule.span_mono (Set.image_mono h)

theorem span_image_iSup {κ : Sort*} (U : κ → Submodule K V) :
    Submodule.span ℂ (j '' ((⨆ i, U i : Submodule K V) : Set V))
      = ⨆ i, Submodule.span ℂ (j '' (U i : Set V)) := by
  rw [Submodule.iSup_eq_span, span_image_span, Set.image_iUnion, Submodule.span_iUnion]

theorem span_image_bot : Submodule.span ℂ (j '' ((⊥ : Submodule K V) : Set V)) = ⊥ := by
  simp

theorem span_image_sup (U U' : Submodule K V) :
    Submodule.span ℂ (j '' ((U ⊔ U' : Submodule K V) : Set V))
      = Submodule.span ℂ (j '' (U : Set V)) ⊔ Submodule.span ℂ (j '' (U' : Set V)) := by
  rw [← Submodule.span_eq U, ← Submodule.span_eq U', ← Submodule.span_union, span_image_span,
    Set.image_union, Submodule.span_union, span_image_span, span_image_span]

variable {ι : Type} [Finite ι] (b : Module.Basis ι K V)

include b in
theorem finiteDimensional_of_basis : FiniteDimensional K V := Module.Finite.of_basis b

theorem span_image_top (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) :
    Submodule.span ℂ (j '' ((⊤ : Submodule K V) : Set V)) = ⊤ := by
  rw [eq_top_iff, ← hsp]
  exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨b k, Submodule.mem_top, rfl⟩)

theorem finiteDimensional_W (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) : FiniteDimensional ℂ W :=
  Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)

theorem finrank_W (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) :
    Module.finrank ℂ W = Module.finrank K V := by
  haveI := Fintype.ofFinite ι
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge), Module.finrank_eq_card_basis b]

theorem linearIndependent_comp (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    {κ : Type} {u : κ → V} (hu : LinearIndependent K u) :
    LinearIndependent ℂ (fun k => j (u k)) := by
  haveI := finiteDimensional_of_basis b
  have hs : LinearIndepOn K id (Set.range u) := hu.linearIndepOn_id
  let B := Module.Basis.extend hs
  haveI : Fintype (hs.extend (Set.subset_univ _)) := Fintype.ofFinite _
  have hB : LinearIndependent ℂ (fun l => j (B l)) := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
    · rw [← hsp]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      have h1 : j (b k) ∈ Submodule.span ℂ (j '' (Submodule.span K (Set.range B) : Set V)) := by
        rw [B.span_eq]; exact Submodule.subset_span ⟨b k, Submodule.mem_top, rfl⟩
      rw [span_image_span, ← Set.range_comp] at h1
      exact h1
    · rw [finrank_W j b hli hsp, Module.finrank_eq_card_basis B]
  let f : κ → hs.extend (Set.subset_univ _) := fun k => ⟨u k, Module.Basis.subset_extend hs ⟨k, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hu.injective (congrArg Subtype.val h)
  have := hB.comp f hf
  convert this using 1
  funext k
  simp [B, f, Module.Basis.coe_extend]

theorem finrank_span_image (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (U : Submodule K V) :
    Module.finrank ℂ (Submodule.span ℂ (j '' (U : Set V))) = Module.finrank K U := by
  haveI := finiteDimensional_of_basis b
  let bU := Module.finBasis K U
  have hu : LinearIndependent K (fun i => (bU i : V)) :=
    bU.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hspan : Submodule.span K (Set.range fun i => (bU i : V)) = U := by
    have : (Set.range fun i => (bU i : V)) = U.subtype '' Set.range bU := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bU.span_eq, Submodule.map_subtype_top]
  have h2 : Submodule.span ℂ (j '' (U : Set V))
      = Submodule.span ℂ (Set.range fun i => j (bU i : V)) := by
    conv_lhs => rw [← hspan]
    rw [span_image_span, ← Set.range_comp]; rfl
  rw [h2, finrank_span_eq_card (linearIndependent_comp j b hli hsp hu), Fintype.card_fin]

theorem span_image_inf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (U U' : Submodule K V) :
    Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V))
      = Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  refine Submodule.eq_of_le_of_finrank_eq
    (le_inf (span_image_mono j inf_le_left) (span_image_mono j inf_le_right)) ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U U'
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℂ (j '' (U : Set V)))
    (Submodule.span ℂ (j '' (U' : Set V)))
  rw [← span_image_sup] at h2
  simp only [finrank_span_image j b hli hsp] at h2 ⊢
  omega

theorem span_image_finset_inf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) {I : Type} (U : I → Submodule K V)
    (F : Finset I) :
    Submodule.span ℂ (j '' ((F.inf U : Submodule K V) : Set V))
      = F.inf (fun i => Submodule.span ℂ (j '' (U i : Set V))) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.inf_empty]; exact span_image_top j b hsp
  | insert i F hi ih => rw [Finset.inf_insert, Finset.inf_insert, span_image_inf j b hli hsp, ih]

theorem exists_finset_inf_eq_iInf {I : Type} [FiniteDimensional K V] (U : I → Submodule K V) :
    ∃ F : Finset I, F.inf U = ⨅ i, U i := by
  classical
  have hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n := ⟨_, ∅, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩
  have hle : (insert i F).inf U ≤ F.inf U := Finset.inf_mono (Finset.subset_insert i F)
  have hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V)) := Nat.find_min' hex ⟨_, rfl⟩
  have heq : (insert i F).inf U = F.inf U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i F)

theorem span_image_iInf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) {I : Type} (U : I → Submodule K V) :
    Submodule.span ℂ (j '' ((⨅ i, U i : Submodule K V) : Set V))
      = ⨅ i, Submodule.span ℂ (j '' (U i : Set V)) := by
  haveI := finiteDimensional_of_basis b
  obtain ⟨F, hF⟩ := exists_finset_inf_eq_iInf U
  refine le_antisymm (le_iInf fun i => span_image_mono j (iInf_le U i)) ?_
  rw [← hF, span_image_finset_inf j b hli hsp]
  exact Finset.le_inf fun i _ => iInf_le _ i

theorem span_image_ker (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (f : Module.End K V)
    (fC : Module.End ℂ W) (hf : ∀ v, j (f v) = fC (j v)) :
    Submodule.span ℂ (j '' (LinearMap.ker f : Set V)) = LinearMap.ker fC := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  have hle : Submodule.span ℂ (j '' (LinearMap.ker f : Set V)) ≤ LinearMap.ker fC := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hv ⊢
    rw [← hf, hv, map_zero]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hr : LinearMap.range fC = Submodule.span ℂ (j '' (LinearMap.range f : Set V)) := by
    rw [LinearMap.range_eq_map, ← span_image_top j b hsp, Submodule.map_span, LinearMap.range_eq_map,
      Submodule.map_coe, Set.image_image, Set.image_image]
    simp_rw [hf]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker fC
  rw [hr, finrank_span_image j b hli hsp, finrank_W j b hli hsp] at h2
  rw [finrank_span_image j b hli hsp]
  omega

theorem span_image_maxGenEigenspace (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (f : Module.End K V)
    (fC : Module.End ℂ W) (hf : ∀ v, j (f v) = fC (j v)) (a : K) :
    Submodule.span ℂ (j '' (f.maxGenEigenspace a : Set V)) = fC.maxGenEigenspace (σ a) := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  have key : ∀ (k : ℕ) (v : V),
      ((fC - σ a • (1 : Module.End ℂ W)) ^ k) (j v) = j (((f - a • (1 : Module.End K V)) ^ k) v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smulₛₗ, hf]
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat,
    Module.End.genEigenspace_nat, finrank_W j b hli hsp]
  exact span_image_ker j b hli hsp _ _ (fun v => (key _ v).symm)

end GlobalTheory.ScalarExtEig

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open GlobalTheory.ScalarExtEig in

theorem span_image_eigAt_of_basis : ∀ {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V) (opC : I → Module.End ℂ W), LinearIndependent ℂ (fun k => j (b k)) → Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ → (∀ i x, j (op i x) = opC i (j x)) → (∀ s : I → K, Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) = Formalism.L2.Col.eigAt opC (fun i => σ (s i))) ∧ (∀ Q : (I → K) → Prop, Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V)) = Formalism.L2.Col.eigSum opC (fun x => ∃ s, Q s ∧ x = fun i => σ (s i))) ∧ (Formalism.L2.Col.PairComm op → Formalism.L2.Col.SplitOver op → ∀ x, Formalism.L2.Col.Occurs opC x → ∃ s, Formalism.L2.Col.Occurs op s ∧ x = fun i => σ (s i)) := by
  intro K V W I ι _ _ _ _ _ _ σ j b op opC hli hsp hop
  have h1 : ∀ s : I → K, Submodule.span ℂ (j '' (eigAt op s : Set V))
      = eigAt opC (fun i => σ (s i)) := by
    intro s
    rw [eigAt, span_image_iInf j b hli hsp, eigAt]
    exact iInf_congr fun i => span_image_maxGenEigenspace j b hli hsp (op i) (opC i) (hop i) (s i)
  refine ⟨h1, fun Q => ?_, fun hc hs x hx => ?_⟩
  · unfold eigSum
    simp_rw [span_image_iSup, h1]
    apply le_antisymm
    · exact iSup₂_le fun s hs => le_iSup₂_of_le (f := fun (y : I → ℂ) (_ : ∃ s, Q s ∧ y = fun i => σ (s i)) => eigAt opC y) _ ⟨s, hs, rfl⟩ le_rfl
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨s, hs, rfl⟩ := hy
      exact le_iSup₂_of_le (f := fun (s : I → K) (_ : Q s) => eigAt opC (fun i => σ (s i))) s hs le_rfl
  · by_contra hno
    push_neg at hno
    have hcC : PairComm opC := by
      intro i k
      show opC i * opC k = opC k * opC i
      refine LinearMap.ext_on_range hsp fun m => ?_
      have := congrArg (fun g => j (g (b m))) (hc i k).eq
      simpa [Module.End.mul_apply, hop] using this
    haveI := finiteDimensional_of_basis b
    have htop : (⊤ : Submodule ℂ W) ≤ ⨆ (y : I → ℂ) (_ : y ≠ x), eigAt opC y := by
      rw [← span_image_top j b hsp, ← iSup_eigAt_eq_top hc hs, span_image_iSup]
      refine iSup_le fun s => ?_
      by_cases hs0 : Occurs op s
      · rw [h1]
        exact le_iSup₂_of_le (f := fun (y : I → ℂ) (_ : y ≠ x) => eigAt opC y) _ (hno s hs0).symm le_rfl
      · rw [Occurs, not_not] at hs0
        rw [hs0, span_image_bot]
        exact bot_le
    exact hx (disjoint_top.1 (((iSupIndep_eigAt hcC) x).mono_right htop))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegral
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.StabLoc

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem mem_range_iff (m : GL n R) :
    m ∈ (Formalism.UG.bc (n := n) O.subtype).range ↔
      ∀ y : n → R, (∀ i, y i ∈ O) ↔ ∀ i, m.1.mulVec y i ∈ O := by
  have key : ∀ (A : Matrix n n R), (∀ i j, A i j ∈ O) → ∀ y : n → R, (∀ i, y i ∈ O) →
      ∀ i, A.mulVec y i ∈ O := fun A hA y hy i =>
    O.sum_mem fun j _ => O.mul_mem (hA i j) (hy j)
  have hs : ∀ j i : n, (Pi.single j (1 : R) : n → R) i ∈ O := by
    intro j i
    by_cases h : i = j
    · subst h; simp [O.one_mem]
    · simp [h, O.zero_mem]
  constructor
  · rintro ⟨k, rfl⟩ y
    refine ⟨key _ (fun i j => (k.1 i j).2) y, fun h => ?_⟩
    have := key (Formalism.UG.bc (n := n) O.subtype k⁻¹).1 (fun i j => ((k⁻¹).1 i j).2) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at this
  · intro h
    have h1 : ∀ i j, m.1 i j ∈ O := fun i j => by
      simpa using (h (Pi.single j 1)).1 (hs j) i
    have h2 : ∀ i j, (m⁻¹).1 i j ∈ O := fun i j => by
      have := (h ((m⁻¹).1.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hs j) i
      rwa [Matrix.mulVec_single_one] at this
    let A : Matrix n n O := Matrix.of fun i j => ⟨m.1 i j, h1 i j⟩
    let B : Matrix n n O := Matrix.of fun i j => ⟨(m⁻¹).1 i j, h2 i j⟩
    have hA : O.subtype.mapMatrix A = m.1 := rfl
    have hB : O.subtype.mapMatrix B = (m⁻¹).1 := rfl
    have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n R) :=
      fun X Y hXY => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hXY i) j)
    refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end Ring

theorem stab_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E))
    (hh : IsFrameAt V v h) (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔
      h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  have hloc : Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
    constructor
    · intro hs x
      have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
        funext fun i => evF_sgT_ne hw _
      have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
      have := hs fun i => sgT E v (x i)
      rw [mem_lamHat_iff, mem_lamHat_iff] at this
      simp only [hev] at this
      constructor
      · intro h0
        have h1 := this.1 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw]; exact zero_mem _) v
        rwa [hxv] at h1
      · intro h0
        have h1 := this.2 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
        rwa [hxv] at h1
    · intro hs y
      rw [mem_lamHat_iff, mem_lamHat_iff]
      refine forall_congr' fun w => ?_
      rw [hev]
      by_cases hw : w = v
      · subst hw; exact hs _
      · rw [hg w hw, Units.val_one, Matrix.one_mulVec]
  rw [hloc, mem_range_iff]
  constructor
  · intro hs y
    have := hs (h.1.mulVec y)
    rw [hh, hh, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rwa [Units.val_mul, Units.val_mul]
  · intro hs x
    have := hs ((h⁻¹).1.mulVec x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul,
      ← Matrix.mulVec_mulVec] at this
    rw [hh, hh]
    exact this

end GlobalTheory.PlaceComp.StabLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
section
noncomputable section

namespace GlobalTheory.BlockType

open GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_one_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {h : GL n k} (hh : h ∈ KO k n) (a b : n) :
    valuation k (h.val a b) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hh
  exact (g.val a b).2

theorem val_col_lt {n : Type} [Fintype n] [DecidableEq n] {h g : GL n k} (hh : h ∈ KO k n) (b : n)
    (hg : ∀ c, valuation k ((g.val - 1) c b) < 1) (a : n) : valuation k ((h.val * (g.val - 1)) a b) < 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun c _ => by
    rw [map_mul]; exact Right.mul_lt_one_of_le_of_lt (val_le_one_of_mem_KO hh a c) (hg c)

variable (k) in

def blockGrp (r t : ℕ) : Subgroup (GL (Fin (r + t)) k) where
  carrier := {h | h ∈ KO k (Fin (r + t)) ∧
    ∀ (a : Fin (r + t)) (j : Fin r), valuation k ((h.val - 1) a (Fin.castAdd t j)) < 1}
  one_mem' := ⟨(KO k _).one_mem, fun a j => by simp⟩
  mul_mem' := by
    rintro h g ⟨hh, h1⟩ ⟨hg, g1⟩
    refine ⟨(KO k _).mul_mem hh hg, fun a j => ?_⟩
    have e : ((h * g).val - 1) = h.val * (g.val - 1) + (h.val - 1) := by
      simp only [Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_lt _ (val_col_lt hh _ (fun c => g1 c j) a) (h1 a j)
  inv_mem' := by
    rintro h ⟨hh, h1⟩
    refine ⟨(KO k _).inv_mem hh, fun a j => ?_⟩
    have e : ((h⁻¹ : GL (Fin (r + t)) k).val - 1) = -((h⁻¹ : GL (Fin (r + t)) k).val * (h.val - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]; abel
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    exact val_col_lt ((KO k _).inv_mem hh) _ (fun c => h1 c j) a

open Classical in

def blockChar {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) : ℂ :=
  if hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 0 then 0 else (χ (Units.mk0 _ hd) : ℂ)

theorem blockChar_eq {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) (u : kˣ)
    (hu : (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) : blockChar χ h = χ u := by
  have hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := hu ▸ u.ne_zero
  rw [blockChar, dif_neg hd]
  congr 2
  ext; simp [hu]

theorem mem_blockGrp {r t : ℕ} {h : GL (Fin (r + t)) k} (hK : h ∈ KO k (Fin (r + t)))
    (h1 : ∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1)
    (h2 : ∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) :
    h ∈ blockGrp k r t := by
  refine ⟨hK, fun a j => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · have := h2 i j
    simpa [Matrix.sub_apply, Matrix.one_apply, Fin.castAdd_inj] using this
  · have := h1 i j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simpa [Matrix.sub_apply, Matrix.one_apply, hne] using this

theorem isBlockVec_of {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W)
    (hv : ∀ h ∈ blockGrp k r t, π h v = blockChar χ h • v) : GlobalTheory.SplitRead.IsBlockVec χ π v := by
  intro h hK h1 h2 u hu
  rw [hv h (mem_blockGrp hK h1 h2), blockChar_eq χ h u hu]

theorem kOne_le_blockGrp (r t : ℕ) : KOne k (Fin (r + t)) ≤ blockGrp k r t := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨⟨g, rfl⟩, fun a j => ?_⟩
  have hg' : ∀ a b, IsLocalRing.residue 𝒪[k] (g.val a b) = (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a b := by
    intro a b
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val a b) hg
    simpa using this
  have hm : g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hg']
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e]
  have := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val - 1) a (Fin.castAdd t j) =
      ((g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) : 𝒪[k]) : k) := by
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e] <;> rfl
  rw [e]; exact this

theorem blockChar_kOne {r t : ℕ} (χ : kˣ →* ℂˣ) (hχ : IsTame χ) {h : GL (Fin (r + t)) k}
    (hh : h ∈ KOne k (Fin (r + t))) : blockChar χ h = 1 := by
  obtain ⟨g, hg, rfl⟩ := hh
  have hg' : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val) hg
    ext a b
    have h2 := congrArg (fun M : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k] => M (Fin.natAdd r a) (Fin.natAdd r b)) this
    simpa [Matrix.one_apply, Fin.natAdd_inj] using h2
  have hm : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, RingHom.map_det, RingHom.mapMatrix_apply, hg', Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    rw [show ((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : k) =
      algebraMap 𝒪[k] k (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  have hne : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) ≠ 0 := by
    intro h0
    have : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 : 𝒪[k]) : k) = -1 := by
      push_cast; rw [h0]; ring
    rw [this, Valuation.map_neg, map_one] at hv
    exact lt_irrefl _ hv
  rw [blockChar_eq χ _ (Units.mk0 _ hne) e.symm, hχ (Units.mk0 _ hne) (by simpa using hv)]
  simp

end GlobalTheory.BlockType
end
end

