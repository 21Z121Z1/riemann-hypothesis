import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0028
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0027

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AeComm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_rep_conj_chi_smul_and_q_twisted {K : Type} [Field K] {n : ℕ} (u v r ri r' ri' : Matrix (Fin n) (Fin n) K) (e : K)
    (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1) (hr' : r' * ri' = 1)
    (hA : rᵀ * u * r' = e • u) (X : Matrix (Fin n) (Fin n) K) :
    -(v * (r * X * ri)ᵀ * u) = r' * -(v * Xᵀ * u) * ri' := by
  have hrT : riᵀ * rᵀ = 1 := by rw [← Matrix.transpose_mul, hr, Matrix.transpose_one]
  have h1 : u * r' = e • (riᵀ * u) := by
    calc u * r' = riᵀ * (rᵀ * u * r') := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrT, Matrix.one_mul]
      _ = e • (riᵀ * u) := by rw [hA, Matrix.mul_smul]
  have h2 : ∀ Z, r' * (v * Z) = e • (v * (riᵀ * Z)) := by
    intro Z
    calc r' * (v * Z) = v * (u * r') * (v * Z) := by
          rw [← Matrix.mul_assoc v u r', hvu, Matrix.one_mul]
      _ = e • (v * (riᵀ * Z)) := by
          rw [h1]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc u v Z, huv, Matrix.one_mul]
  have hA' : rᵀ * (u * r') = e • u := by rw [← Matrix.mul_assoc]; exact hA
  have h3 : -(v * (r * X * ri)ᵀ * u) * r' = r' * -(v * Xᵀ * u) := by
    simp only [Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hA', h2,
      Matrix.mul_smul]
  calc -(v * (r * X * ri)ᵀ * u) = -(v * (r * X * ri)ᵀ * u) * (r' * ri') := by
        rw [hr', Matrix.mul_one]
    _ = r' * -(v * Xᵀ * u) * ri' := by rw [← Matrix.mul_assoc, h3]

private theorem u_mul_ri_mul_v_eq_transpose_of_eigen {K : Type} [Field K] {n : ℕ} (u v A r ri : Matrix (Fin n) (Fin n) K) (e : K)
    (he : e ≠ 0) (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1)
    (h1 : A * u * r = e • u) (h2 : A * uᵀ * r = e • uᵀ) : u * ri * v = uᵀ * ri * vᵀ := by
  have huvT : uᵀ * vᵀ = 1 := by rw [← Matrix.transpose_mul, hvu, Matrix.transpose_one]
  have hA1 : A = e • (u * ri * v) := by
    calc A = A * u * r * ri * v := by
          rw [Matrix.mul_assoc (A * u) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A u v, huv,
            Matrix.mul_one]
      _ = e • (u * ri * v) := by rw [h1, Matrix.smul_mul, Matrix.smul_mul]
  have hA2 : A = e • (uᵀ * ri * vᵀ) := by
    calc A = A * uᵀ * r * ri * vᵀ := by
          rw [Matrix.mul_assoc (A * uᵀ) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A uᵀ vᵀ, huvT,
            Matrix.mul_one]
      _ = e • (uᵀ * ri * vᵀ) := by rw [h2, Matrix.smul_mul, Matrix.smul_mul]
  exact smul_right_injective _ he (hA1.symm.trans hA2)

private theorem neg_conj_neg_transpose_eq_self_of_symm {K : Type} [Field K] {n : ℕ} (u v X : Matrix (Fin n) (Fin n) K)
    (hvu : v * u = 1) (hS : u * X * v = uᵀ * X * vᵀ) : -(v * (-(v * Xᵀ * u))ᵀ * u) = X := by
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc uᵀ X vᵀ, ← hS, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  simp only [Matrix.mul_assoc]
  rw [hvu, Matrix.mul_one, ← Matrix.mul_assoc, hvu, Matrix.one_mul]

theorem UpperTheory.V.Ws.Eb.adExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K), Full ρ → F.IsForm O n ρ P →
        ∃ R : Representation K F.Γ (Matrix (Fin n) (Fin n) K), IsAdExt F ρ P R := by
  intro l _ F O _ _ K _ _ n ρ P hFull hForm
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hcc' : ∀ x : F.Γ, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hconjv : ∀ g : F.G₀, ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c := by
    intro g
    show F.c * ↑g * F.c⁻¹ = _
    rw [hci]
  have hconj2 : ∀ g : F.G₀, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    rw [hconjv, hconjv]
    simp only [mul_assoc, hcc, mul_one, hcc']
  have heps : ∀ g : F.G₀, F.eps O K (F.conj g) = F.eps O K g := by
    intro g
    simp [W.GFrame.eps, W.GFrame.conj, W.pushCh]
  have hF : ∀ g : F.G₀, (↑(ρ g) : Matrix (Fin n) (Fin n) K)ᵀ * (↑P : Matrix (Fin n) (Fin n) K) *
      (↑(ρ (F.conj g)) : Matrix (Fin n) (Fin n) K) =
      ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (↑P : Matrix (Fin n) (Fin n) K) := hForm
  have huv : (↑P : Matrix (Fin n) (Fin n) K) * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv P
  have hvu : (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * (↑P : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul P
  have hS : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑P : Matrix (Fin n) (Fin n) K) * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) =
      (↑P : Matrix (Fin n) (Fin n) K)ᵀ * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ := by
    intro X
    have hX : X ∈ Submodule.span K (Set.range (W.mat ρ)) := by
      have h : Submodule.span K (Set.range (W.mat ρ)) = ⊤ := hFull
      rw [h]
      exact Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have e1 := hF (F.conj h⁻¹)
      rw [hconj2] at e1
      have e2 := congrArg Matrix.transpose (hF h⁻¹)
      rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, ← Matrix.mul_assoc, ← heps h⁻¹] at e2
      refine u_mul_ri_mul_v_eq_transpose_of_eigen _ _ ((↑(ρ (F.conj h⁻¹)) : Matrix (Fin n) (Fin n) K)ᵀ) (↑(ρ h⁻¹)) _ _
        (Units.ne_zero _) huv hvu ?_ e1 e2
      show (↑(ρ h⁻¹) : Matrix (Fin n) (Fin n) K) * (↑(ρ h) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul a x _ hx => simp only [Matrix.mul_smul, Matrix.smul_mul, hx]
  let θ : Module.End K (Matrix (Fin n) (Fin n) K) :=
    { toFun := fun X => -((↑P⁻¹ : Matrix (Fin n) (Fin n) K) * Xᵀ * (↑P : Matrix (Fin n) (Fin n) K))
      map_add' := fun X Y => by
        simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
      map_smul' := fun a X => by
        simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
          RingHom.id_apply] }
  have hkey : ∀ g : F.G₀, θ * Loc.adGL ρ g = Loc.adGL ρ (F.conj g) * θ := by
    intro g
    apply LinearMap.ext
    intro X
    exact exists_rep_conj_chi_smul_and_q_twisted _ _ _ _ _ _ _ huv hvu (Units.mul_inv _) (Units.mul_inv _) (hF g) X
  have hθθ : θ * θ = 1 := by
    apply LinearMap.ext
    intro X
    exact neg_conj_neg_transpose_eq_self_of_symm _ _ X hvu (hS X)
  have hker : ∀ γ : F.Γ, F.η γ ≠ 1 → γ * F.c ∈ F.η.ker := by
    intro γ h
    rw [MonoidHom.mem_ker, map_mul, F.η_c]
    rcases Int.units_eq_one_or (F.η γ) with h' | h'
    · exact absurd h' h
    · rw [h']
      exact Int.units_mul_self _
  have hAd : ∀ x y : F.G₀, (x : F.Γ) = y → Loc.adGL ρ x = Loc.adGL ρ y := by
    intro x y hxy
    rw [Subtype.ext hxy]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  let f : F.Γ → Module.End K (Matrix (Fin n) (Fin n) K) := fun γ =>
    if h : F.η γ = 1 then Loc.adGL ρ ⟨γ, h⟩ else Loc.adGL ρ ⟨γ * F.c, hker γ h⟩ * θ
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ⟨?_, ?_⟩⟩
  · show f 1 = 1
    simp only [f, dif_pos (map_one F.η)]
    exact map_one (Loc.adGL ρ)
  · intro a b
    show f (a * b) = f a * f b
    have hab : F.η (a * b) = F.η a * F.η b := map_mul _ _ _
    rcases Int.units_eq_one_or (F.η a) with ha | ha <;>
      rcases Int.units_eq_one_or (F.η b) with hb | hb
    · have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb, one_mul]
      simp only [f, dif_pos ha, dif_pos hb, dif_pos h1]
      rw [← map_mul (Loc.adGL ρ)]
      exact hAd _ _ rfl
    · have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, one_mul]; exact hne
      simp only [f, dif_pos ha, dif_neg hb', dif_neg h1]
      rw [← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [mul_assoc])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, mul_one]; exact hne
      simp only [f, dif_neg ha', dif_pos hb, dif_neg h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, hkey, ← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc'])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb]; exact Int.units_mul_self _
      simp only [f, dif_neg ha', dif_neg hb', dif_pos h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, ← mul_assoc θ, hkey, mul_assoc (Loc.adGL ρ _) θ θ, hθθ,
        mul_one, ← map_mul (Loc.adGL ρ)]
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc, hcc'])
  · intro g X
    show f ↑g X = _
    simp only [f, dif_pos (MonoidHom.mem_ker.mp g.2)]
  · intro X
    show f F.c X = _
    have hn : ¬ F.η F.c = 1 := by rw [F.η_c]; exact hne
    simp only [f, dif_neg hn]
    rw [Module.End.mul_apply]
    have h1 : ∀ p, (⟨F.c * F.c, p⟩ : F.G₀) = 1 := fun p => Subtype.ext hcc
    rw [h1, map_one]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AwAvg
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_coboundary_on_h_of_vanish_on_finiteIndex {K : Type*} [Field K] [CharZero K] {Γ : Type*} [Group Γ] {M : Type*}
    [AddCommGroup M] [Module K M] (R : Representation K Γ M) (z : Γ → M)
    (hco : ∀ g h, z (g * h) = z g + R g (z h)) (H N : Subgroup Γ) [N.FiniteIndex]
    (hN : ∀ g ∈ H, g ∈ N → z g = 0) :
    ∃ X, ∀ g ∈ H, z g = R g X - X := by
  classical
  have hQ : Finite (H ⧸ N.subgroupOf H) := inferInstance
  letI : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  have hzout : ∀ (g : H) (q : H ⧸ N.subgroupOf H),
      z (((g • q).out : H) : Γ) = z g + R g (z ((q.out : H) : Γ)) := by
    intro g q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (N.subgroupOf H) (g * q.out)
    have hq : g • q = (QuotientGroup.mk (g * q.out) : H ⧸ N.subgroupOf H) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hk]
    have hk0 : z ((k : H) : Γ) = 0 := hN _ (k : H).2 (Subgroup.mem_subgroupOf.mp k.2)
    simp only [Subgroup.coe_mul, hco, hk0, map_zero, add_zero]
  have hm : ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨-(((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K)⁻¹ •
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)), fun g hg => ?_⟩
  have hsum : ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) =
      ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g +
        R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) := by
    calc ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)
        = ∑ q : H ⧸ N.subgroupOf H, z (((((⟨g, hg⟩ : H) • q)).out : H) : Γ) :=
          (Fintype.sum_equiv (MulAction.toPerm (⟨g, hg⟩ : H)) _ _ (fun q => rfl)).symm
      _ = ∑ q : H ⧸ N.subgroupOf H, (z g + R g (z ((q.out : H) : Γ))) :=
          Finset.sum_congr rfl (fun q _ => hzout ⟨g, hg⟩ q)
      _ = _ := by
          rw [Finset.sum_add_distrib, map_sum, Finset.sum_const, Finset.card_univ,
            Nat.cast_smul_eq_nsmul]
  have hR : R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) =
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) -
        ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum.symm
  rw [map_neg, map_smul, hR, smul_sub, smul_smul, inv_mul_cancel₀ hm, one_smul]
  abel

theorem UpperTheory.V.Ws.Eb.bkAw :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), V.S' = s.S → ∀ {c : Coef l} {n : ℕ} (r : W.Resid V.frame c.O n) (R : Representation (PadicAlgCl l) V.frame.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))), ∀ z ∈ Z1 R, (∀ u, ∀ g ∈ r.Ip u, z g = 0) → (∀ g ∈ V.frame.I0, z g = 0) →
        ∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal → ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w), z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X := by
  intro l _ L Ω _ _ _ _ _ _ s V hS c n r R z hz hIp hI0 w hw
  classical
  have hco : ∀ g h, z (g * h) = z g + R g (z h) := hz.2
  have hz1 : z 1 = 0 := by simpa using hco 1 1
  by_cases hwS : w ∈ V.S'
  swap
  · refine ⟨0, fun g hg => ?_⟩
    have hg1 : toGS Ω V.S' g = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.le_topologicalClosure _
        (Subgroup.subset_normalClosure
          (Set.mem_iUnion₂.mpr ⟨w, hwS, Set.mem_iUnion₂.mpr ⟨s.A w, s.hA w, hg⟩⟩)))
    rw [map_zero, sub_zero]
    exact (congrArg z hg1).trans hz1
  have hlift : ∀ g ∈ Ine (F := W.Lp L) (s.A w), ∃ h ∈ Ine (F := L) (s.A w),
      ((V.pr h : V.η.ker) : GS Ω V.S') = toGS Ω V.S' g := by
    intro g hg
    obtain ⟨h, rfl⟩ := s.unr (s.A w) w (s.hA w) hg
    exact ⟨h, hg, rfl⟩
  rw [hS] at hwS
  rcases hwS with hl | hSt | h0
  · exact absurd hl hw
  · let N : Subgroup V.frame.Γ := (⨅ i, (r.chib i).ker).map V.frame.η.ker.subtype
    let H : Subgroup V.frame.Γ := (V.frame.Iu ⟨w, hSt⟩).map V.frame.η.ker.subtype
    haveI : N.FiniteIndex := by
      have h1 : Finite (V.frame.G₀ ⧸ (⨅ i, (r.chib i).ker)) :=
        Subgroup.quotient_finite_of_isOpen' V.frame.η.ker _ V.frame.η_open (by
          rw [Subgroup.coe_iInf]
          exact isOpen_iInter_of_finite (fun i => r.chib_open i))
      have h2 : Finite (V.frame.Γ ⧸ V.frame.η.ker) :=
        Subgroup.quotient_finite_of_isOpen _ V.frame.η_open
      exact ⟨by
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite⟩
    have hN : ∀ g ∈ H, g ∈ N → z g = 0 := by
      intro g hgH hgN
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hgH
      obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.mp hgN
      have hba : b = a := Subtype.ext hab
      subst hba
      exact hIp ⟨w, hSt⟩ b ⟨ha, hb⟩
    obtain ⟨X, hX⟩ := exists_coboundary_on_h_of_vanish_on_finiteIndex R z hco H N hN
    refine ⟨X, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh]
    exact hX _ ⟨V.pr h, ⟨h, hh, rfl⟩, rfl⟩
  · subst h0
    refine ⟨0, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh, map_zero, sub_zero]
    exact hI0 _ ⟨h, hh, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.BkAbEmb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

open scoped Pointwise in
private theorem bkAb_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω) (hA : ∀ w, IsPlaceOver (A w) w)
    (τ : F →+* Formalism.BasicNotions.Loc.Om l) :
    ∃ (j : Ω →+* Formalism.BasicNotions.Loc.Om l) (w : HeightOneSpectrum (𝓞 F)), j.comp (algebraMap F Ω) = τ ∧
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ Loc.placeJ j = A w := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨j₀, hj₀⟩ : ∃ j : Ω →+* Formalism.BasicNotions.Loc.Om l, j.comp (algebraMap F Ω) = τ := by
    letI : Algebra F (Formalism.BasicNotions.Loc.Om l) := τ.toAlgebra
    exact ⟨(IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).toRingHom,
      (IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).comp_algebraMap⟩
  obtain ⟨w, hw, hl⟩ := ((Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j₀).1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA w) hw
  refine ⟨j₀.comp (g : Ω →+* Ω), w, hj₀ ▸ RingHom.ext fun x => congrArg j₀ (g.commutes x), hl, ?_⟩
  ext x
  change g • x ∈ Loc.placeJ j₀ ↔ _
  rw [← hg]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

theorem UpperTheory.V.Ws.Eb.bkAb :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {n : ℕ} (R : Representation (PadicAlgCl l) V.frame.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))), ∀ z ∈ Z1 R,
        (∀ (v : V.frame.Vl) (φ : V.frame.Gv v →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ → (∀ g, φ g ∈ Loc.Iq l ↔ g ∈ V.frame.Iv v) → (∀ g, Loc.cycA l l (PadicAlgCl l) (φ g) = cycBar L Ω l (Subtype.val g)) →
          (fun g : V.frame.Gv v => z (V.frame.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (V.frame.η.ker.subtype.comp (V.frame.φ v)) : Representation (PadicAlgCl l) (V.frame.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l)))) →
        (∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal → ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w), z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X) →
        Af.IsBK l (R.comp (toGS Ω V.S') : Representation (PadicAlgCl l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) (fun g => z (toGS Ω V.S' g)) := by
  intro l _ L Ω _ _ _ _ _ _ s V n R z hz h1 h2
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  refine ⟨fun w hw => ⟨s.A w, s.hA w, h2 w hw⟩, fun τ => ?_⟩
  obtain ⟨j, w, hj, hl, hA⟩ := bkAb_emb s.A s.hA τ
  refine ⟨j, hj, ?_⟩
  have key : ∃ φ : ↥(Dec (F := L) (s.A w)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
      (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A w)) ∧
      (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
    rw [← hA]
    obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
    exact ⟨φ, a, b, c, d l⟩
  obtain ⟨φ, a, b, c, d⟩ := key
  have h3 := h1 ⟨w, hl⟩ φ a c fun g => congrArg (Units.map _) (d g)
  exact (Loc.bkAbove (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A w)).subtype) a b
    (R.comp (toGS Ω V.S')) (fun g => z (toGS Ω V.S' g))
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩).1 h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cocExt_mem {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {x : F.Γ} (hx : x ∉ F.η.ker) : x * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η x) with h | h
  · exact absurd h hx
  · rw [h]
    rfl

private theorem cocycle_extends_to_conj_group {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K M : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (R : Representation K F.Γ M) (y : F.G₀ → M) (w : M)
    (hy : Continuous y) (hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h))
    (hw : Continuous fun g : F.G₀ => R g w) (hcw : R F.c w = -w)
    (hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w)) :
    ∃ z : F.Γ → M, Continuous z ∧ (∀ g h, z (g * h) = z g + R g (z h)) ∧ ∀ g : F.G₀, z g = y g := by
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hc2 : ∀ x : F.Γ, x * F.c * F.c = x := fun x => by rw [mul_assoc, hcc, mul_one]
  have I1 : ∀ g h : F.Γ, g * F.c * (F.c * h * F.c) = g * h * F.c := fun g h => by
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hcc, one_mul]
  have I2 : ∀ g h : F.Γ, g * F.c * (F.c * (h * F.c) * F.c) = g * h := fun g h => by
    simp only [mul_assoc]
    rw [hcc, mul_one, ← mul_assoc F.c F.c, hcc, one_mul]
  have hker : IsOpen (F.η.ker : Set F.Γ) := F.η_open
  have hkerc : IsOpen (F.η.ker : Set F.Γ)ᶜ := (Subgroup.isClosed_of_isOpen _ hker).isOpen_compl
  have Rm : ∀ (a b : F.Γ) (v : M), R (a * b) v = R a (R b v) := fun a b v => by rw [map_mul]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have hneg : ∀ x : F.Γ, x ∉ F.η.ker → F.η x = -1 := fun x hx => by
    rcases Int.units_eq_one_or (F.η x) with h | h
    · exact absurd (MonoidHom.mem_ker.mpr h) hx
    · exact h
  let z : F.Γ → M := fun x =>
    if hx : x ∈ F.η.ker then y ⟨x, hx⟩ else y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w
  have zin : ∀ x (hx : x ∈ F.η.ker), z x = y ⟨x, hx⟩ := fun x hx => dif_pos hx
  have zout : ∀ x (hx : x ∉ F.η.ker), z x = y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w :=
    fun x hx => dif_neg hx
  refine ⟨z, ?_, ?_, fun g => zin g g.2⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ F.η.ker
    · apply ContinuousOn.continuousAt _ (hker.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : (F.η.ker : Set F.Γ) => (⟨p.1, p.2⟩ : F.G₀) :=
        continuous_subtype_val.subtype_mk fun p => p.2
      refine (hy.comp hm).congr fun p => ?_
      exact (zin p.1 p.2).symm
    · apply ContinuousOn.continuousAt _ (hkerc.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : ((F.η.ker : Set F.Γ)ᶜ : Set F.Γ) => (⟨p.1 * F.c, cocExt_mem F p.2⟩ : F.G₀) :=
        (continuous_subtype_val.mul continuous_const).subtype_mk _
      refine ((hy.comp hm).add (hw.comp hm)).congr fun p => ?_
      exact (zout p.1 p.2).symm
  · intro g h
    by_cases hg : g ∈ F.η.ker <;> by_cases hh : h ∈ F.η.ker
    · rw [zin _ (mul_mem hg hh), zin _ hg, zin _ hh]
      exact hyc ⟨g, hg⟩ ⟨h, hh⟩
    · have hgh : g * h ∉ F.η.ker := fun H => hh (by simpa using mul_mem (inv_mem hg) H)
      rw [zout _ hgh, zin _ hg, zout _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g, hg⟩ * ⟨h * F.c, cocExt_mem F hh⟩ :=
        Subtype.ext (mul_assoc _ _ _)
      rw [e, hyc, map_add, ← Rm, ← mul_assoc]
      exact add_assoc _ _ _
    · have hgh : g * h ∉ F.η.ker := fun H => hg (by simpa using mul_mem H (inv_mem hh))
      rw [zout _ hgh, zout _ hg, zin _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h, hh⟩ := by
        apply Subtype.ext
        show g * h * F.c = g * F.c * ((F.conj ⟨h, hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I1 g h).symm
      rw [e, hyc, hrel, map_add, map_sub]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h, hh⟩)) = R g (y ⟨h, hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h, hh⟩)) w) = R (g * h * F.c) w := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * h * F.c)) w = _
        rw [I1]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - R (g * h * F.c) w)) + R (g * h * F.c) w = y _ + R (g * F.c) w + R g _
      abel
    · have hgh : g * h ∈ F.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, hneg g hg, hneg h hh]
        decide
      rw [zin _ hgh, zout _ hg, zout _ hh]
      have e : (⟨g * h, hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h * F.c, cocExt_mem F hh⟩ := by
        apply Subtype.ext
        show g * h = g * F.c * ((F.conj ⟨h * F.c, cocExt_mem F hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I2 g h).symm
      rw [e, hyc, hrel, map_add, map_sub, map_add]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h * F.c, cocExt_mem F hh⟩)) =
          R g (y ⟨h * F.c, cocExt_mem F hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h * F.c, cocExt_mem F hh⟩)) w) =
          -R g (R (h * F.c) w) := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * (h * F.c) * F.c)) w = _
        rw [I2, ← Rm, ← mul_assoc, Rm (g * h) F.c, hcw, map_neg, neg_neg]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - -R g (R (h * F.c) w))) = y _ + R (g * F.c) w + (R g _ + R g (R (h * F.c) w))
      abel

theorem UpperTheory.V.Ws.Eb.cocExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)), Full ρ → Continuous ρ → IsAdExt F ρ P R →
        ∀ y ∈ Z1 (Loc.adGL ρ), ∀ Z, (∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z)) → ∃ z ∈ Z1 R, ∀ g : F.G₀, z g = y g := by
  intro l _ F K _ _ _ _ n ρ P R hF hρ hA y hy Z hZ
  obtain ⟨hy0, hycoc⟩ := hy
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have Rm : ∀ (a b : F.Γ) (v : Matrix (Fin n) (Fin n) K), R (a * b) v = R a (R b v) :=
    fun a b v => by rw [map_mul]; rfl
  have Rcc : ∀ v, R F.c (R F.c v) = v := fun v => by rw [← Rm, hcc, map_one]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have cc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    rw [hconj, hconj]
    simp only [← mul_assoc, hcc, one_mul]
    rw [mul_assoc, hcc, mul_one]
  have hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h) := fun g h => by
    rw [hycoc g h, hA.ad]
  have hinv : ∀ g : F.G₀, R g (Z + R F.c Z) = Z + R F.c Z := by
    intro g
    have e2 := hZ (F.conj g)
    rw [cc, hZ g, map_add, Rcc, map_sub, ← Rm, hconj] at e2
    have ec : F.c * (F.c * (g : F.Γ) * F.c) = g * F.c := by
      rw [← mul_assoc, ← mul_assoc, hcc, one_mul]
    rw [ec, Rm] at e2
    rw [map_add, ← sub_eq_zero, ← neg_eq_zero]
    rw [← sub_eq_zero] at e2
    rw [← e2]
    abel
  set w : Matrix (Fin n) (Fin n) K := (2 : K)⁻¹ • (R F.c Z - Z) with hwdef
  have hcw : R F.c w = -w := by
    rw [hwdef, map_smul, map_sub, Rcc, ← smul_neg, neg_sub]
  have hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w) := by
    intro g
    rw [hZ g]
    congr 1
    have hi := hinv (F.conj g)
    rw [map_add] at hi
    rw [hwdef, map_smul, map_sub, ← smul_sub]
    have hb : R (F.conj g) (R F.c Z) = Z + R F.c Z - R (F.conj g) Z := by
      rw [← hi]
      abel
    rw [hb]
    have e : R F.c Z - Z - (Z + R F.c Z - R (↑(F.conj g)) Z - R (↑(F.conj g)) Z) =
        (2 : K) • (R (↑(F.conj g)) Z - Z) := by
      rw [two_smul]
      abel
    rw [e, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hw : Continuous fun g : F.G₀ => R g w := by
    have e : (fun g : F.G₀ => R g w) =
        fun g => (↑(ρ g) : Matrix (Fin n) (Fin n) K) * w * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
      funext fun g => by rw [hA.ad]; rfl
    rw [e]
    exact ((Units.continuous_val.comp hρ).matrix_mul continuous_const).matrix_mul (Units.continuous_coe_inv.comp hρ)
  obtain ⟨z, hz, hzc, hzy⟩ := cocycle_extends_to_conj_group F R y w hy0 hyc hw hcw hrel
  exact ⟨z, ⟨hz, hzc⟩, hzy⟩
end

