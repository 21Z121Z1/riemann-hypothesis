import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0024
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem conjugate_diagonal_zero_of_parity {R : Type} [CommRing R] {n : ℕ} (p q : Fin n → Bool)
    (w wi Z : Matrix (Fin n) (Fin n) R) (h1 : w * wi = 1) (h2 : wi * w = 1)
    (hw : ∀ i j, p i ≠ q j → w i j = 0) (hZ : ∀ i j, p i = p j → Z i j = 0) (i : Fin n) :
    (wi * Z * w) i i = 0 := by
  classical
  set P : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if p k then (1 : R) else 0) with hP
  set Q : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if q k then (1 : R) else 0) with hQ
  have hPw : P * w = w * Q := by
    ext a b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : p a = q b
    · rw [hab, mul_comm]
    · rw [hw a b hab]; simp
  have hQwi : Q * wi = wi * P := by
    calc Q * wi = (wi * w) * Q * wi := by rw [h2, Matrix.one_mul]
      _ = wi * (w * Q) * wi := by rw [Matrix.mul_assoc wi w Q]
      _ = wi * (P * w) * wi := by rw [hPw]
      _ = wi * P * (w * wi) := by simp only [Matrix.mul_assoc]
      _ = wi * P := by rw [h1, Matrix.mul_one]
  have hwi : ∀ a b, p b ≠ q a → wi a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun hQwi a) b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    cases hpa : p b <;> cases hqa : q a <;> simp_all
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : p j = q i
  · by_cases hk : p k = q i
    · rw [hZ j k (hj.trans hk.symm)]; ring
    · rw [hw k i hk]; ring
  · rw [hwi i j hj]; ring

theorem UpperTheory.V.Pa.oddDiag :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (R : Type) [CommRing R] [Algebra x.A R] (v : L.Vl), x.wX R v * x.wiX R v = 1 ∧ x.wiX R v * x.wX R v = 1 ∧ (∀ Z ∈ Od x.A R n x.a, ∀ i, (x.wiX R v * Z * x.wX R v) i i = 0) ∧ (∀ g, (∀ i j, j < i → (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i j = 0) ∧ ∀ i, (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i i = algebraMap x.A R (x.ψ v i g)) ∧ (∀ g g', x.ρX R (g * g') = x.ρX R g * x.ρX R g') ∧ x.ρX R 1 = 1 ∧ (∀ g, x.ρX R g ∈ Ev x.A R n x.a) ∧ ∀ g, (x.ρX R g)ᵀ * x.ρX R (G0.frame.conj g) = algebraMap x.A R ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) R) := by
  intro l _ L G G0 h n x R _ _ v
  have hmat : ∀ g, mat x.ρ g = ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) := fun g => rfl
  have hconj : ∀ g, x.wiX R v * x.ρX R g * x.wX R v =
      ((((x.w v)⁻¹ * x.ρ g * x.w v : GL (Fin n) x.A)) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A R) := by
    intro g
    simp only [NP.wX, NP.wiX, NP.ρX, hmat, Units.val_mul, Matrix.map_mul]
  have hw1 : x.wX R v * x.wiX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hw2 : x.wiX R v * x.wX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨hw1, hw2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ i
    refine conjugate_diagonal_zero_of_parity (fun k => decide ((k : ℕ) < x.a)) (x.ty v) _ _ Z hw1 hw2 ?_ ?_ i
    · intro a b hab
      simp only [NP.wX, Matrix.map_apply]
      rw [x.w_blk v a b hab, map_zero]
    · intro a b hab
      have := (hZ a b).1 (by simpa using hab)
      simpa using this
  · intro g
    have t := x.tri v g
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hconj, Matrix.map_apply]
      exact (congrArg (algebraMap x.A R) (t.1 i j hij)).trans (map_zero _)
    · rw [hconj, Matrix.map_apply]
      exact congrArg (algebraMap x.A R) (t.2 i)
  · intro g g'
    simp only [NP.ρX, map_mul, Matrix.map_mul]
  · simp only [NP.ρX, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro g i j
    have hb := x.blk g i j
    refine ⟨fun _ => Submodule.mem_top, fun hn => ?_⟩
    have h0 := hb.2 hn
    rw [Submodule.mem_bot] at h0 ⊢
    simp only [NP.ρX, Matrix.map_apply, h0, map_zero]
  · intro g
    have e := x.form g
    have e2 := congrArg (fun M => M.map (algebraMap x.A R)) e
    simp only [Units.val_one, Matrix.mul_one] at e2
    simp only [NP.ρX, ← Matrix.transpose_map, ← Matrix.map_mul]
    rw [e2]
    ext i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, GFrame.eps, hij]
    · simp [Matrix.one_apply, GFrame.eps, hij]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OoExKer
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ooEx_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K := by
  refine { complete := ?_, isLocalHom := ?_, res_surj := ?_ }
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).mpr hna
    have hk : RingHom.ker (algebraMap O K) = maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ h)
    rw [← hk, RingHom.mem_ker] at hm
    rw [hm] at ha
    exact not_isUnit_zero ha
  · intro x
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

private theorem ooEx_ker (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) (π : O) (hπ : maximalIdeal O = Ideal.span {π}) :
    RingHom.ker (PowerSeries.map (algebraMap O K)) = Ideal.span {PowerSeries.C π} := by
  have hk : RingHom.ker (algebraMap O K) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ h)
  have hπ0 : algebraMap O K π = 0 := by
    rw [← RingHom.mem_ker, hk, hπ]
    exact Ideal.mem_span_singleton_self π
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hc : ∀ n, ∃ c, PowerSeries.coeff n x = π * c := by
      intro n
      have h1 : algebraMap O K (PowerSeries.coeff n x) = 0 := by
        have := congrArg (PowerSeries.coeff n) hx
        simpa using this
      have h2 : PowerSeries.coeff n x ∈ maximalIdeal O := by
        rw [← hk, RingHom.mem_ker]
        exact h1
      rw [hπ, Ideal.mem_span_singleton] at h2
      exact h2
    choose c hc using hc
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hc]
  · rintro ⟨y, rfl⟩
    rw [map_mul, PowerSeries.map_C, hπ0, map_zero, zero_mul]

private theorem ooEx_ev (K O B : Type) [Field K] [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra O K] [CommRing B] [Algebra O B] [IsCO O B]
    (f : B →ₐ[O] PowerSeries K) (s : B) (h : Function.Surjective (algebraMap O K)) (hs : f s = PowerSeries.X) :
    ∃ F : PowerSeries O →+* B, (∀ c : O, F (PowerSeries.C c) = algebraMap O B c) ∧ F PowerSeries.X = s ∧
      ∀ x, f (F x) = PowerSeries.map (algebraMap O K) x := by
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hK : IsCO O K := ooEx_co O K h
  haveI hPK : IsCO O (MvPowerSeries Unit K) := co_mvps O K Unit
  have hsm : s ∈ maximalIdeal B := by
    by_contra hns
    have hu : IsUnit s := by
      by_contra h'
      exact hns ((IsLocalRing.mem_maximalIdeal s).mpr h')
    have hX : IsUnit (PowerSeries.X : PowerSeries K) := hs ▸ hu.map f
    rw [PowerSeries.isUnit_iff_constantCoeff] at hX
    simp at hX
  obtain ⟨G, ⟨hGC, hGX⟩, -⟩ := co_ev O O B Unit (Algebra.ofId O B) (fun _ => s) (fun _ => hsm)
  refine ⟨G.toRingHom, ?_, ?_, ?_⟩
  · intro c
    exact hGC c
  · exact hGX ()
  · let M : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K :=
      { MvPowerSeries.map (algebraMap O K) with
        commutes' := fun c => by
          simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
          exact MvPowerSeries.map_C _ _ }
    have hXm : MvPowerSeries.X () ∈ maximalIdeal (MvPowerSeries Unit K) := by
      refine (IsLocalRing.mem_maximalIdeal _).mpr ?_
      intro hu
      rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
      simp at hu
    obtain ⟨H, -, hU⟩ := co_ev O O (MvPowerSeries Unit K) Unit (Algebra.ofId O _)
      (fun _ => MvPowerSeries.X ()) (fun _ => hXm)
    have e1 : (f.comp G : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K) = H := by
      refine hU _ ⟨fun x => ?_, fun u => ?_⟩
      · simp [hGC]
      · simp only [AlgHom.comp_apply, hGX, hs]
        rfl
    have e2 : M = H := by
      refine hU _ ⟨fun x => ?_, fun u => ?_⟩
      · simp [M, MvPowerSeries.algebraMap_apply]
      · simp [M]
    intro x
    have := congrArg (fun φ : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K => φ x) (e1.trans e2.symm)
    exact this

theorem UpperTheory.V.Pa.ooEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite K] [Algebra O K] [CommRing B] [Algebra O B] [IsCO O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K) (s : B) (rF : Bh →+* FractionRing (PowerSeries K)), Function.Surjective (algebraMap O K) → f s = PowerSeries.X → IsCplAt B (RingHom.ker f) Bh → (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) → ∃ (OO : Type) (_ : CommRing OO) (_ : IsDomain OO) (_ : IsDiscreteValuationRing OO) (_ : IsAdicComplete (maximalIdeal OO) OO) (_ : Algebra OO Bh) (_ : IsCO OO Bh), (∀ a : PowerSeries K, ∃ (o : OO) (b : B), algebraMap OO Bh o = algebraMap B Bh b ∧ f b = a) ∧ (∀ c : O, ∃ o : OO, algebraMap OO Bh o = algebraMap B Bh (algebraMap O B c)) ∧ (∃ o : OO, algebraMap OO Bh o = algebraMap B Bh s) ∧ Function.Surjective (rF.comp (algebraMap OO Bh)) := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ _ _ _ _ f s rF hsur hs hcpl hrF
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ := hπirr.maximalIdeal_eq
  obtain ⟨F, hFC, hFX, hfF⟩ := ooEx_ev K O B f s hsur hs
  have hker := ooEx_ker O K hsur π hπ
  have hmapsurj : Function.Surjective (PowerSeries.map (algebraMap O K)) := by
    intro a
    choose g hg using hsur
    refine ⟨PowerSeries.mk (fun n => g (PowerSeries.coeff n a)), ?_⟩
    ext n
    simp [hg]
  obtain ⟨p, hp⟩ : ∃ p : Ideal (PowerSeries O), p = Ideal.span {PowerSeries.C π} := ⟨_, rfl⟩
  rw [← hp] at hker
  haveI hpP : p.IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime _
  have hπ0 : PowerSeries.C π ≠ 0 := by
    intro h0
    apply hπirr.ne_zero
    have := congrArg PowerSeries.constantCoeff h0
    simpa using this
  have hprime : Prime (PowerSeries.C π) := (Ideal.span_singleton_prime hπ0).mp (hp ▸ hpP)
  have hcO : IsCplAt (PowerSeries O) p (CplAt (PowerSeries O) p) := isCplAt_cplAt _ p
  obtain ⟨hdom, hdvr, -⟩ := IsCplAt.dvr (PowerSeries O) (PowerSeries.C π) hprime
    (CplAt (PowerSeries O) p) (hp ▸ hcO)
  let φ : PowerSeries O →+* Bh := (algebraMap B Bh).comp F
  have hcomapF : Ideal.comap F (RingHom.ker f) = p := by
    rw [← hker]
    ext x
    simp only [Ideal.mem_comap, RingHom.mem_ker, hfF]
  have hφ : Ideal.comap φ (maximalIdeal Bh) = p := by
    rw [← Ideal.comap_comap, hcpl.comap_eq, hcomapF]
  haveI := hcpl.complete
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift (PowerSeries O) p (CplAt (PowerSeries O) p) hcO Bh φ hφ
  letI : Algebra (CplAt (PowerSeries O) p) Bh := ψ.toAlgebra
  letI : Algebra (PowerSeries O) B := F.toAlgebra
  letI : Algebra (PowerSeries O) Bh := φ.toAlgebra
  haveI : IsScalarTower (PowerSeries O) B Bh := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower (PowerSeries O) (CplAt (PowerSeries O) p) Bh :=
    IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hψ x).symm)
  have hCO : IsCO (CplAt (PowerSeries O) p) Bh := by
    refine IsCplAt.isCO (PowerSeries O) B p (RingHom.ker f) (CplAt (PowerSeries O) p) Bh hcO hcpl ?_ ?_
    · exact hcomapF
    · intro x
      obtain ⟨a, ha⟩ := hmapsurj (f x)
      refine ⟨a, ?_⟩
      rw [RingHom.mem_ker, map_sub]
      show f x - f (F a) = 0
      rw [hfF, ha, sub_self]
  have hkey : ∀ c, rF (ψ (algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) c)) =
      algebraMap (PowerSeries K) _ (PowerSeries.map (algebraMap O K) c) := by
    intro c
    have h1 := RingHom.congr_fun hψ c
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    show rF (algebraMap B Bh (F c)) = _
    rw [hrF, hfF]
  refine ⟨CplAt (PowerSeries O) p, inferInstance, hdom, hdvr, hcO.complete, inferInstance, hCO, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨c, hc⟩ := hmapsurj a
    exact ⟨algebraMap _ (CplAt (PowerSeries O) p) c, F c, RingHom.congr_fun hψ c, by rw [hfF, hc]⟩
  · intro c
    refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) (PowerSeries.C c), ?_⟩
    refine (RingHom.congr_fun hψ _).trans ?_
    show algebraMap B Bh (F (PowerSeries.C c)) = _
    rw [hFC]
  · refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) PowerSeries.X, ?_⟩
    refine (RingHom.congr_fun hψ _).trans ?_
    show algebraMap B Bh (F PowerSeries.X) = _
    rw [hFX]
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (PowerSeries K) z
    obtain ⟨cx, hcx⟩ := hmapsurj x
    obtain ⟨cy, hcy⟩ := hmapsurj y
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hcyp : cy ∉ p := by
      rw [← hker, RingHom.mem_ker, hcy]
      exact hy0
    have hunit : IsUnit (algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) cy) := by
      by_contra hu
      apply hcyp
      rw [← hcO.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hu
    obtain ⟨u, hu⟩ := hunit
    refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) cx * ↑u⁻¹, ?_⟩
    rw [map_mul, map_units_inv, RingHom.comp_apply, RingHom.comp_apply]
    show rF (ψ (algebraMap _ (CplAt (PowerSeries O) p) cx)) * (rF (ψ ↑u))⁻¹ = _
    rw [hu, hkey, hkey, hcx, hcy, div_eq_mul_inv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrVr
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prVr :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ g (i j : Fin S.n), S.rF (S.pr0 (S.U.vr g i j)) = S.ρ S.F g i j ∧ ((((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr1 (S.U.vr g i j) = 0) ∧ (¬ (((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr0 (S.U.vr g i j) = 0) := by
  intro l _ S g i j
  have hm : S.U.vr g ∈ blkMat S.n S.x.a (1 : Submodule S.Bh S.U.AA) S.U.N := by
    rw [← S.U.span]; exact Submodule.subset_span ⟨g, rfl⟩
  have hN : S.U.vr g i j - algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ S.U.N := (S.pr1 (S.U.vr g i j)).2
  have hd := Submodule.disjoint_def.1 S.U.compl.disjoint
  have h1 : algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ (1 : Submodule S.Bh S.U.AA) :=
    Submodule.mem_one.2 ⟨_, rfl⟩
  refine ⟨S.U.red g i j _ hN, fun e => ?_, fun e => ?_⟩
  · exact Subtype.ext (hd _ (Submodule.sub_mem _ ((hm i j).1 e) h1) hN)
  · apply S.U.inj
    rw [map_zero]
    refine hd _ h1 ?_
    have := S.U.N.sub_mem ((hm i j).2 e) hN
    rwa [sub_sub_cancel] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PresOut0
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.presOut0 :
    ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] (D0 : ℕ) (X : Fin D0 → B), (∀ a, X a ∈ maximalIdeal B) → maximalIdeal B ≤ Ideal.span (Set.range X) ⊔ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2) → ∀ Z Q : Ideal B, Z.IsPrime → Q.IsPrime → ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Z) → Z ≤ Q := by
  intro O B _ _ _ _ _ _ _ D0 X hX hspan Z Q hZ hQ hdim
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hA : IsCO O (MvPowerSeries (Fin D0) O) := co_mvps O O (Fin D0)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev O O B (Fin D0) (Algebra.ofId O B) X hX
  have hsurj : Function.Surjective F := by
    apply co_surj
    refine le_trans hspan (sup_le ?_ (sup_le ?_ le_sup_right))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_sup_left ?_
      rw [← hFX i]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simp
    · refine le_sup_of_le_left ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h1 : algebraMap O B a = F (MvPowerSeries.C a) := by
        rw [hFC]; rfl
      rw [h1]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simpa using ha
  have hdimA : ringKrullDim (MvPowerSeries (Fin D0) O) = 1 + (D0 : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
  have hinj : ∀ r, F r ∈ Z → r = 0 := by
    intro r hr
    by_contra hne
    have hnz : r ∈ nonZeroDivisors (MvPowerSeries (Fin D0) O) := mem_nonZeroDivisors_of_ne_zero hne
    have hle := ringKrullDim_succ_le_of_surjective ((Ideal.Quotient.mk Z).comp F.toRingHom)
      ((Ideal.Quotient.mk_surjective).comp hsurj) hnz (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hr)
    rw [hdimA] at hle
    generalize ringKrullDim (B ⧸ Z) = d at hle hdim
    have hb : d ≠ ⊥ := ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) hdim
    obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hb
    have h2 : (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := hdim
    rw [WithBot.coe_le_coe] at h2
    have h1 : ((e + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast at hle ⊢; exact hle
    rw [WithBot.coe_le_coe] at h1
    have het : e ≠ ⊤ := by
      intro h; rw [h] at h1; simp at h1
    lift e to ℕ using het
    norm_cast at h1 h2
    omega
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨r, rfl⟩ := hsurj z
    rw [hinj r hz, map_zero]
    exact Ideal.zero_mem _
  rw [hZbot]
  exact bot_le
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RelSub
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section
variable {X : Type} [CommRing X] {a g : ℕ} {c : Fin a → Fin g → X}

private theorem rel_C (r : X) : DD.Rel c (DD.C r) (DD.C r) :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_zero : DD.Rel c 0 0 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_one : DD.Rel c 1 1 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_add {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u + u') (v + v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], by simp [a2, b2], fun k => ?_, fun j => ?_⟩
  · simp [a3, b3, mul_add, Finset.sum_add_distrib]
  · simp [a4, b4, mul_add, Finset.sum_add_distrib]

private theorem rel_neg {u : DD X a} {v : DD X g} (h : DD.Rel c u v) : DD.Rel c (-u) (-v) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  refine ⟨by simp [a1], by simp [a2], fun k => ?_, fun j => ?_⟩
  · simp [a3]
  · simp [a4]

private theorem rel_pair {p q : Fin a → X} {s t : Fin g → X} (h : ∀ k, p k = ∑ j, c k j * s j)
    (h' : ∀ j, t j = ∑ k, c k j * q k) : ∑ k, p k * q k = ∑ j, s j * t j := by
  simp only [h, h', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem rel_mul {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u * u') (v * v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], ?_, fun k => ?_, fun j => ?_⟩
  · have e1 := rel_pair a3 b4
    have e2 := rel_pair b3 a4
    have e3 : ∑ k, u.ep' k * u'.ep k = ∑ j, v.ep' j * v'.ep j := by
      simpa only [mul_comm] using e2
    simp only [DD.mul_eta, Finset.sum_add_distrib, e1, e3, a1, a2, b1, b2]
  · simp only [DD.mul_ep, a3, b3, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [DD.mul_ep', a4, b4, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

private theorem rel_sum {ι : Type} (s : Finset ι) (f : ι → DD X a) (f' : ι → DD X g)
    (h : ∀ i, DD.Rel c (f i) (f' i)) : DD.Rel c (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact rel_add (h i) ih

end

theorem UpperTheory.V.Pa.relSub :
    ∀ (X : Type) [CommRing X] (a g : ℕ) (c : Fin a → Fin g → X), (∀ r : X, DD.Rel c (DD.C r) (DD.C r)) ∧ (∀ u v u' v', DD.Rel c u v → DD.Rel c u' v' → DD.Rel c (u + u') (v + v') ∧ DD.Rel c (u - u') (v - v') ∧ DD.Rel c (u * u') (v * v')) ∧ (∀ u v v', DD.Rel c u v → DD.Rel c u v' → v.ep = v'.ep → v = v') ∧ ∀ (n : ℕ) (l : List (Matrix (Fin n) (Fin n) (DD X a) × Matrix (Fin n) (Fin n) (DD X g))), (∀ p ∈ l, ∀ i j, DD.Rel c (p.1 i j) (p.2 i j)) → ∀ i j, DD.Rel c ((l.map Prod.fst).prod i j) ((l.map Prod.snd).prod i j) := by
  intro X _ a g c
  refine ⟨rel_C, fun u v u' v' h h' => ⟨rel_add h h', ?_, rel_mul h h'⟩, ?_, ?_⟩
  · rw [sub_eq_add_neg, sub_eq_add_neg]
    exact rel_add h (rel_neg h')
  · rintro u v v' ⟨a1, a2, -, a4⟩ ⟨b1, b2, -, b4⟩ e
    exact DD.ext (a1.symm.trans b1) e (funext fun j => (a4 j).trans (b4 j).symm) (a2.symm.trans b2)
  · intro n l
    induction l with
    | nil =>
      intro _ i j
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
      split_ifs
      · exact rel_one
      · exact rel_zero
    | cons p l ih =>
      intro h i j
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      exact rel_sum _ _ _ fun k => rel_mul (h p (List.mem_cons_self ..) i k)
        (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) k j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RfEx
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.rfEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsLocalRing O] [Algebra O K] [CommRing B] [Algebra O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K), IsCplAt B (RingHom.ker f) Bh → ∃ rF : Bh →+* FractionRing (PowerSeries K), (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) ∧ RingHom.ker rF = maximalIdeal Bh := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ f h
  haveI : IsAdicComplete (maximalIdeal (FractionRing (PowerSeries K))) (FractionRing (PowerSeries K)) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let φ : B →+* FractionRing (PowerSeries K) :=
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (f : B →+* PowerSeries K)
  have hcomap : Ideal.comap φ (maximalIdeal (FractionRing (PowerSeries K))) = RingHom.ker f := by
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    ext b
    simp only [RingHom.mem_ker, φ, RingHom.comp_apply, RingHom.coe_coe]
    exact map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift B (RingHom.ker f) Bh h (FractionRing (PowerSeries K)) φ hcomap
  refine ⟨ψ, fun b => RingHom.congr_fun hψ b, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hm
    have hu : IsUnit x := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hm
      exact hm
    exact (hu.map ψ).ne_zero (RingHom.mem_ker.mp hx)
  · have hm := IsCplAt.map_pow_eq B (RingHom.ker f) Bh h 1
    rw [pow_one, pow_one] at hm
    rw [← hm]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hψ]
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingHom.mem_ker.mp ha, map_zero]
end

