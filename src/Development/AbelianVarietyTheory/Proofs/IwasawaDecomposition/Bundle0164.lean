import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionParamLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.TorsionDegree

theorem exists_torsion_param_lattice (L : PeriodPair) (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let f : ℂ → ℤ →+ (latticeCurve L).toAffine.Point := fun ω =>
    (latticePointHom L).comp (zmultiplesHom ℂ (ω / n))
  have hf : ∀ ω (a : ℤ), f ω a = latticePoint L (a * (ω / n)) := fun ω a => by
    simp [f]
  have h0 : ∀ ω ∈ L.lattice, f ω n = 0 := fun ω hω => by
    rw [hf, latticePoint_eq_zero_iff]
    convert hω using 1
    push_cast
    field_simp
  let t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point :=
    (ZMod.lift n ⟨f L.ω₁, h0 _ L.ω₁_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 0) +
    (ZMod.lift n ⟨f L.ω₂, h0 _ L.ω₂_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 1)
  have ht : ∀ a b : ℤ, t ![(a : ZMod n), (b : ZMod n)] = latticePoint L ((a * L.ω₁ + b * L.ω₂) / n) := by
    intro a b
    simp only [t, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.lift_coe, hf]
    rw [← latticePoint_add]
    congr 1
    ring
  refine ⟨t, (injective_iff_map_eq_zero t).2 fun v hv => ?_, fun P hP => ?_⟩
  · obtain ⟨a, ha⟩ := ZMod.intCast_surjective (v 0)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (v 1)
    have e : v = ![(a : ZMod n), (b : ZMod n)] := by
      ext i; fin_cases i <;> simp [ha, hb]
    rw [e, ht, latticePoint_eq_zero_iff, PeriodPair.mem_lattice] at hv
    obtain ⟨c, d, hcd⟩ := hv
    have h1 : ((a - n * c : ℤ) : ℝ) • L.ω₁ + ((b - n * d : ℤ) : ℝ) • L.ω₂ = 0 := by
      rw [eq_div_iff hn'] at hcd
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hcd
    obtain ⟨h2, h3⟩ := LinearIndependent.pair_iff.1 L.indep _ _ h1
    have h2' : a = n * c := by
      have : a - n * c = 0 := by exact_mod_cast h2
      omega
    have h3' : b = n * d := by
      have : b - n * d = 0 := by exact_mod_cast h3
      omega
    rw [e, h2', h3']
    ext i; fin_cases i <;> simp
  · obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    have h1 : latticePoint L (n • z) = 0 := by
      rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
    rw [latticePoint_eq_zero_iff] at h1
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
    refine ⟨_, (ht a b).trans ?_⟩
    rw [hab, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']

theorem exists_torsion_param (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ W.toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  obtain ⟨t, hi, hs⟩ := exists_torsion_param_lattice L n
  refine ⟨e.toAddMonoidHom.comp t, e.injective.comp hi, fun P hP => ?_⟩
  obtain ⟨v, hv⟩ := hs (e.symm P) (by rw [← map_nsmul, hP, map_zero])
  exact ⟨v, by simp [hv]⟩

theorem exists_linearEquiv {G G' : Type} [AddCommGroup G] [AddCommGroup G'] (n : ℕ) [NeZero n]
    (t : (Fin 2 → ZMod n) →+ G') (hi : Function.Injective t) (hs : ∀ P, n • P = 0 → ∃ v, t v = P)
    (ι φ : G →+ G') (hι : Function.Injective ι) (hφ : Function.Injective φ)
    (hr : ∀ P, n • P = 0 → ∃ Q, ι Q = P) :
    ∃ g : (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n), ∀ v Q, ι Q = t v → φ Q = t (g v) := by
  have hv : ∀ v : Fin 2 → ZMod n, n • v = 0 := fun v => by
    ext i; simp
  have h1 : ∀ v, ∃ Q, ι Q = t v := fun v => hr _ (by rw [← map_nsmul, hv, map_zero])
  choose s hs' using h1
  have h2 : ∀ v, ∃ w, t w = φ (s v) := fun v => hs _ (by
    have : n • s v = 0 := hι (by rw [map_nsmul, hs', ← map_nsmul, hv, map_zero, map_zero])
    rw [← map_nsmul, this, map_zero])
  choose u hu using h2
  have hadd : ∀ v w, u (v + w) = u v + u w := fun v w => hi (by
    rw [map_add, hu, hu, hu, ← map_add]
    congr 1
    exact hι (by rw [map_add, hs', hs', hs', map_add]))
  let U := (AddMonoidHom.mk' u hadd).toZModLinearMap n
  have hU : Function.Injective U := fun v w h => hi (by
    have h' : u v = u w := h
    rw [← hs', ← hs', hφ ((hu v).symm.trans (h' ▸ hu w))])
  refine ⟨LinearEquiv.ofBijective U ⟨hU, Finite.surjective_of_injective hU⟩, fun v Q hQ => ?_⟩
  rw [hι (hQ.trans (hs' v).symm), ← hu]
  rfl

theorem card_linearEquiv (n : ℕ) :
    Nat.card ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) = Nat.card (GL (Fin 2) (ZMod n)) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv

theorem finrank_adjoin_le {k : Type} [Field k] [CharZero k] [Algebra k ℂ] (A : WeierstrassCurve k) [A.IsElliptic]
    (n : ℕ) [NeZero n] [FiniteDimensional k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n))] :
    Module.finrank k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n)) ≤
      Nat.card (GL (Fin 2) (ZMod n)) := by
  classical
  set S := torsionCoords (A.baseChange ℂ) n with hS
  set M := IntermediateField.adjoin k S with hM
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  obtain ⟨t, hi, hs⟩ := exists_torsion_param (A.baseChange ℂ) n
  let m : (M →ₐ[k] ℂ) → (A.baseChange M).toAffine.Point →+ (A.baseChange ℂ).toAffine.Point :=
    fun φ => WeierstrassCurve.Affine.Point.map (W' := A.toAffine) φ
  have hm : ∀ φ, Function.Injective (m φ) := fun φ => WeierstrassCurve.Affine.Point.map_injective φ
  have hpt : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y) (hx : x ∈ M) (hy : y ∈ M),
      (A.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ := fun x y h hx hy =>
    (A.toAffine.baseChange_nonsingular (f := M.val) M.val.injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
  have hr : ∀ P, n • P = 0 → ∃ Q, m M.val Q = P := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact ⟨0, rfl⟩
    · exact ⟨.some _ _ (hpt x y h (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inl rfl⟩)
        (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inr rfl⟩)), rfl⟩
  choose g hg using fun φ => exists_linearEquiv n t hi hs (m M.val) (m φ) (hm _) (hm φ) hr
  have hginj : Function.Injective g := by
    intro φ ψ h
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro z ⟨x, y, hxy, h0, hz⟩
    obtain ⟨v, hv⟩ := hs _ h0
    have hx := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inl rfl⟩
    have hy := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inr rfl⟩
    have e : m φ (.some _ _ (hpt x y hxy hx hy)) = m ψ (.some _ _ (hpt x y hxy hx hy)) := by
      rw [hg φ v _ hv.symm, hg ψ v _ hv.symm, h]
    have e' := WeierstrassCurve.Affine.Point.some.inj e
    rcases hz with rfl | rfl
    · exact e'.1
    · exact e'.2
  rw [← card_linearEquiv, ← AlgHom.card k M ℂ, ← Nat.card_eq_fintype_card]
  have : Finite ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)))
  exact Nat.card_le_card_of_injective g hginj

theorem finrank_sup_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (H : IntermediateField K L) (S : Set L)
    [FiniteDimensional K H] [FiniteDimensional H (IntermediateField.adjoin H S)] :
    FiniteDimensional K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) ∧
      Module.finrank K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) =
        Module.finrank K H * Module.finrank H (IntermediateField.adjoin H S) := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have : IsScalarTower K H (IntermediateField.adjoin H S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Free H (IntermediateField.adjoin H S) := Module.Free.of_divisionRing _ _
  have : Module.Free K H := Module.Free.of_divisionRing _ _
  have h : FiniteDimensional K (IntermediateField.adjoin H S) := Module.Finite.trans H _
  exact ⟨h,
    (Module.finrank_mul_finrank K H (IntermediateField.adjoin H S)).symm⟩

theorem finrank_torsionField_le : ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) [A.IsElliptic], FiniteDimensional ℚ (torsionField d A) ∧ Module.finrank ℚ (torsionField d A) ≤ Module.finrank ℚ (hilbertField d F) * Nat.card (GL (Fin 2) (ZMod 12)) := by
  intro d F _ A _
  have hint : IsIntegral ℚ (sqrtNegNat d) :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [sqrtNegNat_sq]
      exact (isIntegral_natCast d).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat d⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hH : FiniteDimensional ℚ (hilbertField d F) := by
    unfold hilbertField; infer_instance
  set H := hilbertField d F with hHdef
  let A' : WeierstrassCurve H := A.map (IntermediateField.inclusion (le_sup_right : F ≤ H)).toRingHom
  have hA : A'.baseChange ℂ = A.baseChange ℂ := by
    simp only [A', WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rfl
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  have : A'.IsElliptic := by
    simp only [A']
    exact WeierstrassCurve.instIsEllipticMap _ _
  have hfin := finite_torsionCoords (A.baseChange ℂ) 12 (by norm_num)
  have halg := FieldsEx.isAlgebraic_of_torsionCoords_finite F A 12 hfin
  have : Finite (torsionCoords (A'.baseChange ℂ) 12) := hA ▸ hfin.to_subtype
  have hM : FiniteDimensional H (IntermediateField.adjoin H (torsionCoords (A'.baseChange ℂ) 12)) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (halg z (hA ▸ hz)).isIntegral.tower_top
  have hle := finrank_adjoin_le A' 12
  obtain ⟨h1, h2⟩ := finrank_sup_adjoin H (torsionCoords (A'.baseChange ℂ) 12)
  have e : torsionField d A = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A'.baseChange ℂ) 12) := by
    rw [hA]
    rfl
  rw [e]
  exact ⟨h1, h2.le.trans (Nat.mul_le_mul_left _ hle)⟩

end GlobalTheory.Mem.TorsionDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgJetSet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetFin

theorem finAlg_range {E : Type} [Field E] [NumberField E] (f : E →+* ℂ) : FinAlg (Set.range f) := by
  classical
  let b := Module.finBasis ℚ E
  refine (finAlg_of_finite (T := Set.range (f ∘ b)) (Set.finite_range _) ?_).closure.mono ?_
  · rintro _ ⟨i, rfl⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom f.toRatAlgHom
  · rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (Subfield.subset_closure ⟨i, rfl⟩)

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem thInd_congr (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x x' : HomE X.E a b)
    (h : x - x' ∈ mulLat c (homAt S N N')) : A.thInd S N N' c x = A.thInd S N N' c x' := by
  unfold Amb.thInd Amb.liftW
  rw [isLift_congr A S N N' c x x' h]

theorem finite_thInd (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (M c : ℕ)
    (hN : IsSdLat N) (hN' : IsSdLat N') (hM : 0 < M) (hc : 0 < c) :
    (A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b))).Finite := by
  have := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S N N' M c hN.1 hN'.1 hM hc).1
  refine (Set.finite_range fun q : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype) =>
    A.thInd S N N' c (Quotient.out q).1).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, thInd_congr A S N N' c _ _ ?_⟩
  have := (Submodule.Quotient.eq ((mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)).1
    (Quotient.out_eq (Submodule.Quotient.mk ⟨x, hx⟩ : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)))
  exact this

noncomputable def pullLin (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b where
  toFun := A.pullV a b γ γ'
  map_add' z w := by
    funext τ i j
    simp only [Amb.pullV, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' t z := by
    funext τ i j
    simp only [Amb.pullV, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem finAlg_jetSet : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M n : ℕ), X.Ok → 0 < M → A.ESmooth a b → A.ThIndEq a b S M → A.ChiLaw a b → JetAlg A a b S M → (∀ τ, IsAlgebraic ℚ (A.cD τ)) → FinAlg (jetSet A a b S M n) := by
  intro X A a b S M n hX hM hE hT hC hJ hD
  classical
  obtain ⟨Ta, hTa, hTa'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX a
  obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX b
  let Z₀ : Set ℂ := ⋃ N ∈ (Ta : Set _), ⋃ N' ∈ (Tb : Set _), ⋃ c ∈ (M.divisors : Set ℕ),
    ⋃ G ∈ A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b)),
      ⋃ e ∈ {e : DVar X.Tau a b →₀ ℕ | e.degree ≤ n}, {(A.chiF a b N N')⁻¹ * derivAt0 G e}
  have hZ₀ : FinAlg Z₀ := by
    refine finAlg_biUnion Ta.finite_toSet fun N hN => finAlg_biUnion Tb.finite_toSet fun N' hN' =>
      finAlg_biUnion (Finset.finite_toSet _) fun c hc => ?_
    have hc' : c ∣ M := Nat.dvd_of_mem_divisors hc
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    refine finAlg_biUnion (finite_thInd A S N N' M c (hTa N hN) (hTb N' hN') hM hc0) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine finAlg_biUnion (Finsupp.finite_of_degree_le n) fun e _ => finAlg_of_finite (Set.finite_singleton _) ?_
    rintro _ rfl
    exact hJ N N' c x ⟨hTa N hN, hTb N' hN', hc0, hc', hx⟩ e
  have h1 : FinAlg (Set.range A.cD) := finAlg_of_finite (Set.finite_range _) (by rintro _ ⟨τ, rfl⟩; exact hD τ)
  have h2 : FinAlg (⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) :=
    finAlg_biUnion Set.finite_univ fun τ _ => finAlg_range _
  refine ((hZ₀.union h1).union h2).closure.mono ?_
  set K₀ := Subfield.closure ((Z₀ ∪ Set.range A.cD) ∪ ⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) with hK₀
  have hemb : ∀ τ x, X.embC A.σ₀ τ x ∈ K₀ := fun τ x =>
    Subfield.subset_closure (Or.inr (Set.mem_biUnion (Set.mem_univ τ) ⟨x, rfl⟩))
  have hcD : ∀ τ, A.cD τ ∈ K₀ := fun τ => Subfield.subset_closure (Or.inl (Or.inr ⟨τ, rfl⟩))
  rintro _ ⟨N, N', c, x, e, hr, he, rfl⟩
  obtain ⟨N₀, hN₀, γ, rfl⟩ := hTa' N hr.1
  obtain ⟨N₀', hN₀', γ', rfl⟩ := hTb' N' hr.2.1
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : HomE X.E a b, x = γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap :=
    ⟨γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap, by ext v; simp⟩
  have hr₀ : InRange S M c N₀ N₀' x₀ :=
    ⟨hTa _ hN₀, hTb _ hN₀', hr.2.2.1, hr.2.2.2.1, (divLat_gmap_iff S M _ _ _ _ _).1 hr.2.2.2.2⟩
  have hth : A.thInd S (gmap γ.1 N₀) (gmap γ'.1 N₀') c (γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap) =
      fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z) := funext (hT γ γ' N₀ N₀' c x₀ hr₀)
  have key : (A.chiF a b N₀ N₀')⁻¹ * derivAt0 (fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z)) e ∈ K₀ := by
    refine GlobalTheory.Mem.JetChain.derivAt0_comp_mem X.Tau a b n K₀ _ _ _ (indSmooth_of A a b S M hE N₀ N₀' c x₀ hr₀) ?_ ?_ e he
    · intro k τ i j
      show A.pullV a b γ.1 γ'.1 (coordX k) τ i j ∈ K₀
      unfold Amb.pullV
      refine sum_mem fun k' _ => sum_mem fun l _ => mul_mem (mul_mem (hemb _ _) ?_) (hemb _ _)
      unfold coordX
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro e' he'
      refine Subfield.subset_closure (Or.inl (Or.inl ?_))
      refine Set.mem_biUnion hN₀ (Set.mem_biUnion hN₀' (Set.mem_biUnion (x := c) ?_ (Set.mem_biUnion ⟨x₀, hr₀.2.2.2.2, rfl⟩
        (Set.mem_biUnion (x := e') he'.le rfl))))
      exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨hr₀.2.2.2.1, hM.ne'⟩)
  show _ ∈ K₀
  rw [hth, hC γ γ' N₀ N₀' hr₀.1 hr₀.2.1, jetC, mul_inv, mul_assoc, mul_left_comm (A.chiF a b N₀ N₀')⁻¹]
  refine mul_mem (inv_mem (mul_mem (zpow_mem (prod_mem fun τ _ => hemb _ _) _) (zpow_mem (prod_mem fun τ _ => hemb _ _) _)))
    (mul_mem (prod_mem fun k _ => pow_mem (hcD _) _) key)

end GlobalTheory.Mem.Col2.JetFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

def GeneratesAlong (I : W.IdealSheafData) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) : Prop :=
  (⨆ k, g ⁻¹ᵁ L.U k = ⊤) ∧ ∀ (k : L.ι) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ L.U k),
    I.ideal A = Ideal.span (Set.range fun j => (g.appLE (L.U k) A.1 h).hom ((σ j).f k))

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharactersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_wild_of_trivial_tame_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
  first | exact @GlobalTheory.TameWild.cob_lt_one_of_tame | exact GlobalTheory.TameWild.cob_lt_one_of_tame | (intros; apply GlobalTheory.TameWild.cob_lt_one_of_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsolutelyIrreducibleSplitRepOfConstituentModeStatement
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  first | exact @GlobalTheory.SplitCrit.splitRep_of_models | exact GlobalTheory.SplitCrit.splitRep_of_models | (intros; apply GlobalTheory.SplitCrit.splitRep_of_models <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
section
noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

variable {X : Fields} {Pr : Primes X} {R : Ranks}

variable (Pr) in

def admitted (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  (P ∈ Pr.vGs → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)) ∧ (P ∉ Pr.vGs → Between j P h)

theorem isAdmissibleIntegralBasisChange_one (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : admitted Pr j P (1 : AutY X R j) :=
  ⟨fun _ => one_mem _, fun hP => between_of_nf hP (IndefiniteRowSideFullHecke.SandwichNormalForm.nf_one j hP)⟩

def nfMat {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  fun l s => if hs : s.1 < n then (if l = s then 1 else 0)
    else q ^ e ⟨s.1 - n, by omega⟩ * ((if l = s then 1 else 0) + if s.1 = n then Loc.inX E n c z l else 0)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

abbrev CAt (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Subgroup (AutY X R j) :=
  Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h

def ChiMul (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  (∀ r ∈ CAt sel mu cst j P h, chiInv Ch sel mu cst j P h r ≠ 0) ∧
    ∀ r ∈ CAt sel mu cst j P h, ∀ r' ∈ CAt sel mu cst j P h,
      chiInv Ch sel mu cst j P h (r * r') = chiInv Ch sel mu cst j P h r * chiInv Ch sel mu cst j P h r'

def ChiTriv (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  ∀ r ∈ CAt sel mu cst j P h, r ∈ Loc.fixX X.E (R.N j) (cOf R j) → chiInv Ch sel mu cst j P h r = 1

def GrpG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal), hbar ∈ lev.H ↔ ∃ g ∈ prCat (Pr := Pr) cst.sharp j P.1 h,
    ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.mulVec (redV P.1 x)

def ChrG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ (hbar : ↥lev.H) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.1.mulVec (redV P.1 x)) →
    ((lev.lam hbar : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

def GrpQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  lev.H = (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1)

def ChrQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  ∀ (g : ↥lev.H) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) →
    ((lev.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

theorem exists_char {G H K : Type} [Group G] [Group H] [Field K] (C : Subgroup G) (χ : G → K) (Rel : G → H → Prop)
    (hne : ∀ r ∈ C, χ r ≠ 0) (hmul : ∀ r ∈ C, ∀ r' ∈ C, χ (r * r') = χ r * χ r')
    (hs : ∀ h, ∃ r ∈ C, Rel r h) (hm : ∀ r h r' h', Rel r h → Rel r' h' → Rel (r * r') (h * h'))
    (hw : ∀ h, ∀ r ∈ C, ∀ r' ∈ C, Rel r h → Rel r' h → χ r = χ r') :
    ∃ lam : H →* Kˣ, ∀ h, ∀ r ∈ C, Rel r h → ((lam h : Kˣ) : K) = χ r := by
  choose s hsC hsR using hs
  refine ⟨MonoidHom.mk' (fun h => Units.mk0 (χ (s h)) (hne _ (hsC h))) fun a b => Units.ext ?_, fun h r hr hR => ?_⟩
  · simp only [Units.val_mk0, Units.val_mul]
    rw [← hmul _ (hsC a) _ (hsC b)]
    exact hw _ _ (hsC _) _ (mul_mem (hsC a) (hsC b)) (hsR _) (hm _ _ _ _ (hsR a) (hsR b))
  · exact hw _ _ (hsC _) _ hr (hsR _) hR

end GlobalTheory.Mem.Col2.IdxEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgebraicOfEllipticTorsionCoordinatesFiniteStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_of_ellipticTorsionCoordinates_finite : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) (n : ℕ), (torsionCoords (A.baseChange ℂ) n).Finite → ∀ z ∈ torsionCoords (A.baseChange ℂ) n, IsAlgebraic ℚ z := by
  first | exact @GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | exact GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | (intros; apply GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSquareAbsNormConjInvariantMovedPrimesIdeal
section
set_option autoImplicit false

namespace GlobalTheory.SquareNorm

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem exists_eq_mul_map {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) (he : ∀ x, e (e x) = x)
    (𝔡 : Ideal R) : 𝔡 ≠ ⊥ → 𝔡.map (e : R →+* R) = 𝔡 →
      (∀ P : Ideal R, P.IsPrime → 𝔡 ≤ P → P.map (e : R →+* R) ≠ P) →
      ∃ 𝔞 : Ideal R, 𝔡 = 𝔞 * 𝔞.map (e : R →+* R) := by
  have hee : ∀ I : Ideal R, (I.map (e : R →+* R)).map (e : R →+* R) = I := fun I => by
    rw [Ideal.map_map]
    have : (e : R →+* R).comp (e : R →+* R) = RingHom.id R := RingHom.ext he
    rw [this, Ideal.map_id]
  induction 𝔡 using WellFoundedGT.induction with
  | ind 𝔡 ih =>
  intro h0 hinv hmv
  by_cases ht : 𝔡 = ⊤
  · exact ⟨⊤, by rw [ht, Ideal.map_top, Ideal.top_mul]⟩
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal 𝔡 ht
  have hQ : (P.map (e : R →+* R)).IsMaximal := Ideal.IsMaximal.map_bijective (e : R →+* R) e.bijective hP
  have hne := hmv P hP.isPrime hle
  have hle' : 𝔡 ≤ P.map (e : R →+* R) := by
    have := Ideal.map_mono (f := (e : R →+* R)) hle
    rwa [hinv] at this
  have hcop : IsCoprime P (P.map (e : R →+* R)) :=
    Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hQ hne.symm)
  obtain ⟨𝔟, hb⟩ := hcop.mul_dvd (Ideal.dvd_iff_le.2 hle) (Ideal.dvd_iff_le.2 hle')
  have hPQ : P * P.map (e : R →+* R) ≠ 0 := fun h => h0 (by rw [hb, h, zero_mul]; rfl)
  have hb0 : 𝔟 ≠ ⊥ := fun h => h0 (by rw [hb, h, Ideal.mul_bot])
  have hdb : 𝔡 ≤ 𝔟 := Ideal.le_of_dvd ⟨P * P.map (e : R →+* R), by rw [mul_comm]; exact hb⟩
  have hlt : 𝔡 < 𝔟 := by
    refine lt_of_le_of_ne hdb fun h => ?_
    have h1 : P * P.map (e : R →+* R) * 𝔟 = 1 * 𝔟 := by rw [← hb, one_mul, h]
    have h2 := mul_right_cancel₀ hb0 h1
    have h3 : (1 : Ideal R) ≤ P := Ideal.le_of_dvd ⟨_, h2.symm⟩
    rw [Ideal.one_eq_top] at h3
    exact hP.ne_top (top_le_iff.1 h3)
  have hbinv : 𝔟.map (e : R →+* R) = 𝔟 := by
    apply mul_left_cancel₀ hPQ
    rw [← hb]
    conv_rhs => rw [← hinv, hb]
    rw [Ideal.map_mul, Ideal.map_mul, hee, mul_comm P]
  obtain ⟨𝔞, ha⟩ := ih 𝔟 hlt hb0 hbinv fun Q hQ' h => hmv Q hQ' (hdb.trans h)
  refine ⟨P * 𝔞, ?_⟩
  rw [hb, Ideal.map_mul]
  conv_lhs => rw [ha]
  ring

theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (𝔡 : Ideal (𝓞 E)), 𝔡 ≠ ⊥ → 𝔡.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔡 → (∀ P : Ideal (𝓞 E), P.IsPrime → 𝔡 ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) → IsSquare (Ideal.absNorm 𝔡) := by
  intro E _ _ _ H 𝔡 h0 hinv hmv
  have he : ∀ x, H.bar (H.bar x) = x := fun x => RingOfIntegers.ext (by
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  obtain ⟨𝔞, ha⟩ := exists_eq_mul_map H.bar he 𝔡 h0 hinv hmv
  have hN : Ideal.absNorm (𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔞 := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv 𝔞 _ H.bar rfl).toEquiv).symm
  exact ⟨Ideal.absNorm 𝔞, by rw [ha, map_mul, hN]⟩

end GlobalTheory.SquareNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tDat_laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  first | exact @GlobalTheory.Mem.Col2.TDat.laws_of_ok | exact GlobalTheory.Mem.Col2.TDat.laws_of_ok | (intros; apply GlobalTheory.Mem.Col2.TDat.laws_of_ok <;> assumption)
end

