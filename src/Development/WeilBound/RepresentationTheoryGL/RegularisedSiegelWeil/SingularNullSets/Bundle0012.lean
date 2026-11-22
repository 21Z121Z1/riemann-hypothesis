import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0010

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FinitePartMemIntegralAdeles
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

section Gen

theorem tmul_den {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] (x : A) {c : F}
    (hc : c ≠ 0) (b : E) : (x * algebraMap F A c⁻¹) ⊗ₜ[F] (c • b) = x ⊗ₜ[F] b := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_left_comm, ← map_mul,
    mul_inv_cancel₀ hc, map_one, mul_one]

theorem map_smul_basis {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (r : R) (k : ι) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (r • Algebra.TensorProduct.basis R b k) = φ r ⊗ₜ[F] b k := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end Gen

variable {D : D7}

abbrev bA (D : D7) := Algebra.TensorProduct.basis (AF D.host.F) (bE D.host.F D.host.E)

theorem crd_cv (v : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (bV (E := D.host.E) v).repr (cv D v z) k = evFin D.host.F v ((bA D).repr z k) :=
  LIdemEx.repr_map' (evFin D.host.F v) (bE D.host.F D.host.E) z k

theorem finPart_plc_mem (v : Pl D) {t : Fv D.host.F v ⊗[D.host.F] D.host.E} (ht : t ∈ intLoc D.host.F D.host.E v) :
    finPart D (plc D.host.E v t) ∈ intAE D := by
  refine intLoc_induction (p := fun t => finPart D (plc D.host.E v t) ∈ intAE D) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [LinearMap.map_add, RingHom.map_add]; exact add_mem hy hz)
    (fun y hy => by rw [LinearMap.map_neg, RingHom.map_neg]; exact neg_mem hy) ht
  rw [plc_tmul]
  refine AddSubgroup.subset_closure ⟨(iV v a).2, fun w => ?_, x, rfl⟩
  by_cases h : w = v
  · subst h
    show (iV w a).2 w ∈ _
    rw [show (iV w a).2 w = a from GlobalTheory.CompanionTheory.PsiCondLoc.single_self w a]
    exact ha
  · show (iV v a).2 w ∈ _
    rw [show (iV v a).2 w = 0 from GlobalTheory.CompanionTheory.PsiCondLoc.single_ne v a h]
    exact zero_mem _

theorem finPart_mem_of_good {z : AE D} (hb : ∀ v, ¬ IsGood D.host.F D.host.E v → cv D v z = 0)
    (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by
  rw [← (bA D).sum_repr z, map_sum]
  refine sum_mem fun k _ => ?_
  have hN : (den (bE D.host.F D.host.E k) : D.host.F) ≠ 0 := by exact_mod_cast den_ne (bE D.host.F D.host.E k)
  let o : 𝓞 D.host.E := ⟨(den (bE D.host.F D.host.E k) : D.host.E) * bE D.host.F D.host.E k, den_int _⟩
  have ho : (o : D.host.E) = (den (bE D.host.F D.host.E k) : D.host.F) • bE D.host.F D.host.E k := by
    rw [Algebra.smul_def, map_intCast]
    rfl
  have e1 : finPart D ((bA D).repr z k • (bA D) k) =
      sndA D.host.F ((bA D).repr z k) ⊗ₜ[D.host.F] bE D.host.F D.host.E k :=
    map_smul_basis (sndA D.host.F) (bE D.host.F D.host.E) _ k
  rw [e1]
  refine AddSubgroup.subset_closure ⟨sndA D.host.F ((bA D).repr z k) *
    algebraMap D.host.F (Af D.host.F) ((den (bE D.host.F D.host.E k) : D.host.F))⁻¹, fun v => ?_, o,
    by rw [ho]; exact (tmul_den _ hN _).symm⟩
  show evalV D.host.F v (sndA D.host.F ((bA D).repr z k) * algebraMap D.host.F (Af D.host.F) _) ∈ _
  rw [map_mul, AlgHom.commutes]
  have hc : evalV D.host.F v (sndA D.host.F ((bA D).repr z k)) = (bV (E := D.host.E) v).repr (cv D v z) k :=
    (crd_cv v z k).symm
  rw [hc]
  by_cases hv : IsGood D.host.F D.host.E v
  · exact mul_mem ((mem_intLoc_iff hv _).1 (hz v) k) (hv.deninv k)
  · rw [hb v hv, map_zero, Finsupp.zero_apply, zero_mul]
    exact zero_mem _

open Classical in
theorem cv_sub_plc (z : AE D) (B : Finset (Pl D)) (z' : AE D) (hz' : z' = z - ∑ v ∈ B, plc D.host.E v (cv D v z))
    (w : Pl D) : cv D w z' = if w ∈ B then 0 else cv D w z := by
  rw [hz', RingHom.map_sub, map_sum]
  by_cases hw : w ∈ B
  · rw [if_pos hw, Finset.sum_eq_single w (fun v _ hv => compFin_plc_ne (Ne.symm hv) _) (fun h => absurd hw h),
      compFin_plc_self, sub_self]
  · rw [if_neg hw, Finset.sum_eq_zero (fun v hv => compFin_plc_ne (fun h => hw (by rw [h]; exact hv)) _), sub_zero]

open Classical in
theorem finite_part_mem_integral_adeles (z z' : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v)
    (hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite) (B : Finset (Pl D)) (hB : B = hfin.toFinset)
    (hcv : ∀ w, cv D w z' = if w ∈ B then 0 else cv D w z) : finPart D z' ∈ intAE D := by
  refine finPart_mem_of_good (fun v hv => ?_) (fun v => ?_)
  · rw [hcv, if_pos (by rw [hB]; exact (Set.Finite.mem_toFinset hfin).2 hv)]
  · rw [hcv]
    split_ifs
    · exact zero_mem _
    · exact hz v

theorem finPart_mem (z : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by
  have hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite :=
    Filter.eventually_cofinite.1 (eventually_good (F := D.host.F) (E := D.host.E))
  have h1 := finite_part_mem_integral_adeles z _ hz hfin _ rfl (cv_sub_plc z hfin.toFinset _ rfl)
  have e : z = (z - ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z)) + ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z) :=
    (sub_add_cancel _ _).symm
  rw [e, RingHom.map_add, map_sum]
  exact add_mem h1 (sum_mem fun v _ => finPart_plc_mem v (hz v))

theorem infPart_eq_one {z : AE D} (h : ∀ w, compInf D.host.F D.host.E w z = 1) : infPart D z = 1 := by
  let bI := Algebra.TensorProduct.basis (Ainf D.host.F) (bE D.host.F D.host.E)
  apply bI.repr.injective
  refine Finsupp.ext fun k => ?_
  have h1 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) z k
  have h2 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) (1 : AE D) k
  have e1 : infPart D z = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
  have e2 : (1 : Ainf D.host.F ⊗[D.host.F] D.host.E) =
      Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 : AE D) := (map_one _).symm
  rw [e1, e2, h1, h2]
  funext w
  have g1 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) z k
  have g2 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) (1 : AE D) k
  have hz : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) 1 := by
    rw [map_one]; exact h w
  rw [hz] at g1
  exact g1.symm.trans g2

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWD
section
noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped Matrix TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn Filter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7}

theorem exists_fin {p : Pl D → Prop} (h : ∀ᶠ v in cofinite, p v) : ∃ S₀ : Finset (Pl D), ∀ v ∉ S₀, p v :=
  ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => by
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv; exact hv⟩

def IntS (S : Finset (Pl D)) (a : AE D) : Prop := ∀ v ∉ S, cv D v a ∈ intLoc D.host.F D.host.E v

def OffS (S : Finset (Pl D)) (a : AE D) : Prop :=
  (∀ w, compInf D.host.F D.host.E w a = 0) ∧ (∀ v ∈ S, cv D v a = 0) ∧ IntS S a

variable {S : Finset (Pl D)}

theorem IntS.add {a b : AE D} (ha : IntS S a) (hb : IntS S b) : IntS S (a + b) := fun v hv => by
  rw [map_add]; exact add_mem (ha v hv) (hb v hv)

theorem IntS.mul {a b : AE D} (ha : IntS S a) (hb : IntS S b) : IntS S (a * b) := fun v hv => by
  rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)

theorem IntS.neg {a : AE D} (ha : IntS S a) : IntS S (-a) := fun v hv => by
  rw [map_neg]; exact neg_mem (ha v hv)

theorem intS_zero : IntS S (0 : AE D) := fun v _ => by rw [map_zero]; exact zero_mem _

theorem intS_sum {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, IntS S (f i)) : IntS S (∑ i ∈ s, f i) :=
  fun v hv => by rw [map_sum]; exact sum_mem fun i hi => h i hi v hv

theorem IntS.cA {a : AE D} (ha : IntS S a) : IntS S (cA D a) := fun v hv => by
  rw [LIdemEx.cv_cA]; exact sigR_mem_intLoc _ (ha v hv)

theorem OffS.add {a b : AE D} (ha : OffS S a) (hb : OffS S b) : OffS S (a + b) :=
  ⟨fun w => by rw [map_add, ha.1 w, hb.1 w, add_zero], fun v hv => by rw [map_add, ha.2.1 v hv, hb.2.1 v hv, add_zero],
    ha.2.2.add hb.2.2⟩

theorem offS_zero : OffS S (0 : AE D) := ⟨fun w => map_zero _, fun v _ => map_zero _, intS_zero⟩

theorem OffS.neg {a : AE D} (ha : OffS S a) : OffS S (-a) :=
  ⟨fun w => by rw [map_neg, ha.1 w, neg_zero], fun v hv => by rw [map_neg, ha.2.1 v hv, neg_zero], ha.2.2.neg⟩

theorem OffS.mul_left {a b : AE D} (ha : IntS S a) (hb : OffS S b) : OffS S (a * b) :=
  ⟨fun w => by rw [map_mul, hb.1 w, mul_zero], fun v hv => by rw [map_mul, hb.2.1 v hv, mul_zero], ha.mul hb.2.2⟩

theorem OffS.mul_right {a b : AE D} (ha : OffS S a) (hb : IntS S b) : OffS S (a * b) :=
  ⟨fun w => by rw [map_mul, ha.1 w, zero_mul], fun v hv => by rw [map_mul, ha.2.1 v hv, zero_mul], ha.2.2.mul hb⟩

theorem offS_sum {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, OffS S (f i)) : OffS S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact offS_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem OffS.cA {a : AE D} (ha : OffS S a) : OffS S (cA D a) :=
  ⟨fun w => by rw [LIdemEx.compInf_cA, ha.1 w, map_zero], fun v hv => by rw [LIdemEx.cv_cA, ha.2.1 v hv, map_zero],
    ha.2.2.cA⟩

theorem OffS.intS {a : AE D} (ha : OffS S a) : IntS S a := ha.2.2

theorem intOff_iff {a b : ℕ} (x : Mx D a b) : IntOff S x ↔ ∀ i j, IntS S (x i j) :=
  ⟨fun h i j v hv => h v hv i j, fun h v hv i j => h i j v hv⟩

theorem offS_mul_left {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, IntS S (x i j)) (hy : ∀ i j, OffS S (y i j))
    (i : Fin a) (j : Fin c) : OffS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact offS_sum _ _ fun k _ => (hy k j).mul_left (hx i k)

theorem offS_mul_right {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, OffS S (x i j)) (hy : ∀ i j, IntS S (y i j))
    (i : Fin a) (j : Fin c) : OffS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact offS_sum _ _ fun k _ => (hx i k).mul_right (hy k j)

theorem intS_mul {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, IntS S (x i j)) (hy : ∀ i j, IntS S (y i j))
    (i : Fin a) (j : Fin c) : IntS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact intS_sum _ _ fun k _ => (hx i k).mul (hy k j)

theorem offS_trace {a : ℕ} {x : Mx D a a} (hx : ∀ i j, OffS S (x i j)) : OffS S (Matrix.trace x) :=
  offS_sum _ _ fun i _ => hx i i

theorem adj_intS {a b : ℕ} {x : Mx D a b} (hx : ∀ i j, IntS S (x i j)) (i : Fin b) (j : Fin a) : IntS S (adj x i j) :=
  (hx j i).cA

theorem adj_offS {a b : ℕ} {x : Mx D a b} (hx : ∀ i j, OffS S (x i j)) (i : Fin b) (j : Fin a) : OffS S (adj x i j) :=
  (hx j i).cA

theorem exists_rat_int {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ i j, IntS S (rat Q i j) := by
  have h : ∀ᶠ v : Pl D in cofinite, IsGood D.host.F D.host.E v ∧ ∀ i j k,
      algebraMap D.host.F (Fv D.host.F v) ((bE D.host.F D.host.E).repr (Q i j) k) ∈ v.adicCompletionIntegers D.host.F :=
    eventually_good.and (eventually_all.2 fun i => eventually_all.2 fun j => eventually_coord (Q i j))
  obtain ⟨S₀, hS₀⟩ := exists_fin h
  refine ⟨S₀, fun S hS i j v hv => ?_⟩
  obtain ⟨hg, hc⟩ := hS₀ v (fun h => hv (hS h))
  show (1 : Fv D.host.F v) ⊗ₜ[D.host.F] Q i j ∈ _
  refine (mem_intLoc_iff hg _).2 fun k => ?_
  rw [crd_tmul, one_mul]
  exact hc i j k

theorem psi_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ z : AE D, OffS S z → ψ (trA z) = 1 ∧ ψ (halfTr z) = 1 := by
  classical
  obtain ⟨S₁, hS₁⟩ := psi_kernel hψ
  obtain ⟨S₂, hS₂⟩ := exists_fin (eventually_good (F := D.host.F) (E := D.host.E))
  refine ⟨S₁ ∪ S₂, fun S hS z hz => ?_⟩
  have h1 : (trA z).1 = 0 := funext fun w => by rw [trA_fst, hz.1 w, map_zero]; rfl
  have hg : ∀ v ∉ S, IsGood D.host.F D.host.E v := fun v hv =>
    hS₂ v fun h => hv (hS (Finset.mem_union_right _ h))
  have h2 : ∀ v ∈ S, (trA z).2 v = 0 := fun v hv => by rw [trA_snd, hz.2.1 v hv, map_zero]
  have h3 : ∀ v ∉ S, (trA z).2 v ∈ v.adicCompletionIntegers D.host.F := fun v hv => by
    rw [trA_snd]; exact trace_mem (hg v hv) (hz.2.2 v hv)
  have hS1 : S₁ ⊆ S := fun v h => hS (Finset.mem_union_left _ h)
  refine ⟨hS₁ S hS1 _ h1 h2 h3, hS₁ S hS1 _ ?_ ?_ ?_⟩
  · show (algebraMap D.host.F (AF D.host.F) (1 / 2)).1 * (trA z).1 = 0
    rw [h1, mul_zero]
  · intro v hv
    show (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 v * (trA z).2 v = 0
    rw [h2 v hv, mul_zero]
  · intro v hv
    show (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 v * (trA z).2 v ∈ _
    refine mul_mem ?_ (h3 v hv)
    have := (hg v hv).half
    rwa [one_div]

theorem dual_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ v ∉ S₀, ∀ c : Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ t ∈ intLoc D.host.F D.host.E v,
        psiV D.host.F ψ v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (c * t)) = 1) →
      c ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨S₀, hS₀⟩ := exists_fin ((eventually_good (F := D.host.F) (E := D.host.E)).and
    (GlobalTheory.CompanionTheory.PsiCondLoc.psiCond D.host.F ψ hψ))
  refine ⟨S₀, fun v hv c hc => ?_⟩
  obtain ⟨hg, hp⟩ := hS₀ v hv
  refine mem_of_trace hg c fun t ht => (hp _).1 fun s hs => ?_
  have hst : algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) s * t ∈ intLoc D.host.F D.host.E v := by
    refine mul_mem ?_ ht
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact tmul_one_mem hs
  have := hc _ hst
  have e : c * (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) s * t) = s • (c * t) := by
    rw [Algebra.smul_def]; ring
  rw [e, LinearMap.map_smul, smul_eq_mul, mul_comm] at this
  exact this

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKG
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

open Matrix

variable {D : D7} {n : ℕ}

theorem map_one' {T : Type} [CommRing T] (f : AE D →+* T) : (1 : Mx D n n).map f = 1 :=
  Matrix.map_one _ (map_zero f) (map_one f)

theorem map_zero' {T : Type} [CommRing T] (f : AE D →+* T) {m p : ℕ} : (0 : Mx D m p).map f = 0 :=
  Matrix.map_zero _ (map_zero f)

theorem unit_n (Y : Mx D n n) (hY : cj (cA D) Y = Y) :
    cj (cA D) (blk4 1 Y 0 1) * Jm D n * blk4 1 Y 0 1 = Jm D n := by
  rw [conj_block_matrix, cj_one, cj_zero, hY, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

def nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : G D n := (exists_G _ (unit_n Y hY)).choose

theorem mat_nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : mat (nOf Y hY) = blk4 1 Y 0 1 :=
  (exists_G _ (unit_n Y hY)).choose_spec

theorem isN_nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : IsN (nOf Y hY) := ⟨Y, mat_nOf Y hY⟩

theorem cj_Jm : cj (cA D) (Jm D n) = blk4 0 (-1) 1 0 := by
  rw [conj_block_matrix, cj_one, cj_zero, cj_neg, cj_one]

theorem unit_w : cj (cA D) (Jm D n) * Jm D n * Jm D n = Jm D n := by
  rw [cj_Jm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]; simp

def wE (D : D7) (n : ℕ) : G D n := (exists_G _ (unit_w (D := D) (n := n))).choose

theorem mat_wE : mat (wE D n) = Jm D n := (exists_G _ (unit_w (D := D) (n := n))).choose_spec

theorem isW_wE : IsW (wE D n) := mat_wE

theorem mat_wE_inv : mat (wE D n)⁻¹ = blk4 0 (-1) 1 0 :=
  mat_inv_eq (by rw [mat_wE, submatrix_fromBlocks_mul]; simp [block_matrix_one])

theorem mat_conj (Y : Mx D n n) (hY : cj (cA D) Y = Y) :
    mat (wE D n * nOf Y hY * (wE D n)⁻¹) = blk4 1 0 (-Y) 1 := by
  rw [mat_mul, mat_mul, mat_wE, mat_nOf, mat_wE_inv, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]; simp

theorem nOf_mem {S : Finset (Pl D)} (Y : Mx D n n) (hY : cj (cA D) Y = Y) (hinf : Y.map (infPart D) = 0)
    (hS : ∀ v ∈ S, Y.map (cv D v) = 0) (hint : ∀ v ∉ S, IntM v Y) : nOf Y hY ∈ KOff D n S := by
  have hinv : mat (nOf Y hY)⁻¹ = blk4 1 (-Y) 0 1 := mat_inv_eq (by rw [mat_nOf, submatrix_fromBlocks_mul]; simp [block_matrix_one])
  apply mem_KOff
  · rw [mat_nOf, block_matrix_map, hinf, map_one', map_zero', block_matrix_one]
  · intro v hv; rw [mat_nOf, block_matrix_map, hS v hv, map_one', map_zero', block_matrix_one]
  · intro v hv i j
    rw [hinv, mat_nOf]
    exact ⟨integral_block_matrix_iff.2 ⟨IntM.one, hint v hv, IntM.zero, IntM.one⟩ i j,
      integral_block_matrix_iff.2 ⟨IntM.one, (hint v hv).neg, IntM.zero, IntM.one⟩ i j⟩

theorem conj_mem {S : Finset (Pl D)} (Y : Mx D n n) (hY : cj (cA D) Y = Y) (hinf : Y.map (infPart D) = 0)
    (hS : ∀ v ∈ S, Y.map (cv D v) = 0) (hint : ∀ v ∉ S, IntM v Y) :
    wE D n * nOf Y hY * (wE D n)⁻¹ ∈ KOff D n S := by
  have hinv : mat (wE D n * nOf Y hY * (wE D n)⁻¹)⁻¹ = blk4 1 0 Y 1 :=
    mat_inv_eq (by rw [mat_conj, submatrix_fromBlocks_mul]; simp [block_matrix_one])
  have hneg : ∀ {T : Type} [CommRing T] (f : AE D →+* T), (-Y).map f = -(Y.map f) := fun f => Matrix.map_neg _ (map_neg f) _
  apply mem_KOff
  · rw [mat_conj, block_matrix_map, hneg, hinf, neg_zero, map_one', map_zero', block_matrix_one]
  · intro v hv; rw [mat_conj, block_matrix_map, hneg, hS v hv, neg_zero, map_one', map_zero', block_matrix_one]
  · intro v hv i j
    rw [hinv, mat_conj]
    exact ⟨integral_block_matrix_iff.2 ⟨IntM.one, IntM.zero, (hint v hv).neg, IntM.one⟩ i j,
      integral_block_matrix_iff.2 ⟨IntM.one, IntM.zero, hint v hv, IntM.one⟩ i j⟩

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

