import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartCut
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsSmoothQuotientByWeightedEquations
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem quot_facts {O X R R' : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (W : WPres O X R) (h : W.HasOrigin) (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (hh : IsHomog O W.wt (RingHom.ker (p.comp W.π))) (x' : R' →ₐ[O] O) (hx : x'.comp p = W.origin h) :
    ∃ h' : (W.quot p hp hh).HasOrigin, (W.quot p hp hh).origin h' = x' ∧
      (W.quot p hp hh).part = fun j => (W.part j).map p.toLinearMap := by
  have hq : ∀ f : MvPowerSeries W.σ O, p (W.π f) = 0 → MvPowerSeries.constantCoeff f = 0 := by
    intro f hf
    have h1 := congrArg (fun g => g (W.π f)) hx
    simp only [AlgHom.comp_apply, hf, map_zero, WPres.origin_π] at h1
    exact h1.symm
  refine ⟨hq, ?_, ?_⟩
  · ext y
    obtain ⟨z, rfl⟩ := hp y
    obtain ⟨f, rfl⟩ := W.surj z
    have e1 := WPres.origin_π (W.quot p hp hh) hq f
    have e2 := congrArg (fun g => g (W.π f)) hx
    simp only [AlgHom.comp_apply, WPres.origin_π] at e2
    exact e1.trans e2.symm
  · funext j
    show Submodule.map (p.comp W.π).toLinearMap _ = Submodule.map p.toLinearMap (Submodule.map W.π.toLinearMap _)
    rw [← Submodule.map_comp]
    rfl

private theorem der_sq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
  intro g hg
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
  · rw [RingHom.mem_ker] at ha hb
    rw [hD a b, ha, hb, zero_smul, zero_smul, add_zero]
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

private theorem indep {O A κ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [Fintype κ] (x : A →ₐ[O] O)
    (g : κ → A) (hd : ∀ k, ∃ δ ∈ PtDer x O, δ (g k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (g k') = 0) :
    LinearIndependent O (fun i => (satSq x).mkQ (g i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hs : (satSq x).mkQ (∑ i, c i • g i) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hc
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hs
  obtain ⟨a, ha0, ha⟩ := hs
  obtain ⟨δ, hδ, hk, hk'⟩ := hd k
  have hz := der_sq x δ hδ _ ha
  rw [map_smul, map_sum] at hz
  simp only [map_smul, smul_eq_mul] at hz
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hk' j hj, mul_zero]) (by simp)] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h ha0
  · rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hk

private theorem der_desc {O A A' κ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
    (x : A →ₐ[O] O) (g : κ → A) (hg : ∀ k, x (g k) = 0) (p : A →ₐ[O] A') (hp : Function.Surjective p)
    (hk : RingHom.ker p = Ideal.span (Set.range g)) (x' : A' →ₐ[O] O) (hx : x'.comp p = x)
    (δ : A →ₗ[O] O) (hδ : δ ∈ PtDer x O) (h0 : ∀ k, δ (g k) = 0) :
    ∃ δ' ∈ PtDer x' O, ∀ y, δ' (p y) = δ y := by
  have hker : ∀ y, y ∈ Ideal.span (Set.range g) → x y = 0 ∧ δ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact ⟨hg k, h0 k⟩
    | zero => simp
    | add a b _ _ ha hb => simp [ha.1, ha.2, hb.1, hb.2]
    | smul a z _ hz =>
      refine ⟨?_, ?_⟩
      · simp [hz.1]
      · rw [smul_eq_mul, hδ a z, hz.1, hz.2, smul_zero, zero_smul, add_zero]
  have hle : LinearMap.ker p.toLinearMap ≤ LinearMap.ker δ := by
    intro y hy
    have hy' : y ∈ RingHom.ker p := hy
    rw [hk] at hy'
    exact (hker y hy').2
  let e := LinearMap.quotKerEquivOfSurjective p.toLinearMap hp
  let δ' : A' →ₗ[O] O := ((LinearMap.ker p.toLinearMap).liftQ δ hle).comp e.symm.toLinearMap
  have hδ' : ∀ y, δ' (p y) = δ y := by
    intro y
    have : e.symm (p y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [δ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  refine ⟨δ', ?_, hδ'⟩
  intro f g'
  obtain ⟨a, rfl⟩ := hp f
  obtain ⟨b, rfl⟩ := hp g'
  rw [← map_mul, hδ', hδ', hδ', hδ a b]
  have ha : x' (p a) = x a := by rw [← hx]; rfl
  have hb : x' (p b) = x b := by rw [← hx]; rfl
  rw [ha, hb]

theorem UpperTheory.exists_smooth_quotient_by_weighted_equations :
    ∀ (O X : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] (P : Type) [CommRing P] [Algebra O P] [IsCO O P] (W : WPres O X P) (h : W.HasOrigin) (n : X → ℕ), SmoothPt W.part (W.origin h) n → ∀ (κ : Type) [Fintype κ] (g : κ → P) (w : κ → X), (∀ k, g k ∈ W.part (w k) ∧ W.origin h (g k) = 0) → (∀ k, ∃ δ ∈ PtDer (W.origin h) O, δ (g k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (g k') = 0) → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (_ : IsDomain R) (q : P →ₐ[O] R) (W' : WPres O X R) (h' : W'.HasOrigin) (n' : X → ℕ), Function.Surjective q ∧ (∀ s, ∃ s', W'.wt s = W.wt s') ∧ (∀ j, W'.part j = (W.part j).map q.toLinearMap) ∧ (W'.origin h').comp q = W.origin h ∧ (∀ k, q (g k) = 0) ∧ (∀ δ ∈ PtDer (W.origin h) O, (∀ k, δ (g k) = 0) → ∀ y, q y = 0 → δ y = 0) ∧ SmoothPt W'.gr (W'.originA h') n' ∧ ∀ j, n' j + Nat.card {k // w k = j} = n j := by
  intro O X _ _ _ _ _ _ _ _ _ P _ _ _ W h n hs κ _ g w hgw hd
  classical
  obtain ⟨τ, _, wt0, φ, hc, hn⟩ := hs
  set I : Ideal P := Ideal.span (Set.range g) with hI
  have hIx : ∀ a ∈ I, W.origin h a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker (W.origin h) := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact (hgw k).2
    exact hle ha
  let p : P →ₐ[O] P ⧸ I := Ideal.Quotient.mkₐ O I
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective O I
  have hpker : RingHom.ker p = Ideal.span (Set.range g) := by
    rw [← hI]
    exact Ideal.Quotient.mkₐ_ker O I
  let x' : P ⧸ I →ₐ[O] O := Ideal.Quotient.liftₐ I (W.origin h) hIx
  have hx' : x'.comp p = W.origin h := by
    ext y
    rfl
  have hli := indep (W.origin h) g hd
  obtain ⟨τ', _, wt', φ', hc', hn'⟩ :=
    chart_cut O P X W.part (W.origin h) τ wt0 φ hc κ g w hgw hli (P ⧸ I) p x' hp hpker hx'
  have hgA : ∀ k, (⟨g k, W.part_le_A (hgw k).1⟩ : W.A) ∈ W.gr (w k) := fun k => (hgw k).1
  obtain ⟨hhom, -⟩ := homog_span O P X W κ (fun k => ⟨g k, W.part_le_A (hgw k).1⟩) w hgA
  have hh1 : IsHomog O W.wt (RingHom.ker (p.comp W.π)) := by
    have e : RingHom.ker (p.comp W.π) = Ideal.comap W.π (Ideal.span (Set.range fun k => g k)) := by
      ext f
      simp [p, Ideal.Quotient.eq_zero_iff_mem, hI]
    rw [e]
    exact hhom
  obtain ⟨h1, ho1, hpart1⟩ := quot_facts W h p hp hh1 x' hx'
  set W1 := W.quot p hp hh1 with hW1
  have hc1 : IsChart W1.part (W1.origin h1) wt' φ' := by
    rw [ho1, hpart1]
    exact hc'
  obtain ⟨hprime, hhom1, hkle, hdk, hdesc⟩ := chart_ker O X (P ⧸ I) W1 h1 τ' wt' φ' hc1
  set J : Ideal (P ⧸ I) := RingHom.ker φ' with hJ
  have hJx : ∀ a ∈ J, x' a = 0 := by
    intro a ha
    have := hkle ha
    rw [ho1] at this
    exact this
  let p2 : P ⧸ I →ₐ[O] (P ⧸ I) ⧸ J := Ideal.Quotient.mkₐ O J
  have hp2 : Function.Surjective p2 := Ideal.Quotient.mkₐ_surjective O J
  let x'' : (P ⧸ I) ⧸ J →ₐ[O] O := Ideal.Quotient.liftₐ J x' hJx
  let φ'' : (P ⧸ I) ⧸ J →ₐ[O] MvPowerSeries τ' (FractionRing O) :=
    Ideal.Quotient.liftₐ J φ' (fun a ha => ha)
  have hx'' : x''.comp p2 = W1.origin h1 := by
    rw [ho1]
    ext y
    rfl
  have hφ'' : φ''.comp p2 = φ' := by
    ext y
    rfl
  have hc2 := hdesc ((P ⧸ I) ⧸ J) p2 x'' φ'' hp2 hx'' hφ''
  have hh2 : IsHomog O W1.wt (RingHom.ker (p2.comp W1.π)) := by
    have e : RingHom.ker (p2.comp W1.π) = RingHom.ker (φ'.comp W1.π) := by
      ext f
      simp [p2, Ideal.Quotient.eq_zero_iff_mem, hJ]
    rw [e]
    exact hhom1
  obtain ⟨h2, ho2, hpart2⟩ := quot_facts W1 h1 p2 hp2 hh2 x'' hx''
  set W2 := W1.quot p2 hp2 hh2 with hW2
  have hc3 : IsChart W2.part (W2.origin h2) wt' φ'' := by
    rw [ho2, hpart2]
    exact hc2
  have hgr := chart_gr O X ((P ⧸ I) ⧸ J) W2 h2 τ' wt' φ'' hc3
  haveI : J.IsPrime := hprime
  let q : P →ₐ[O] (P ⧸ I) ⧸ J := p2.comp p
  have hq : Function.Surjective q := hp2.comp hp
  have hpartq : ∀ j, W2.part j = (W.part j).map q.toLinearMap := by
    intro j
    rw [hpart2, hpart1]
    show _ = Submodule.map (p2.toLinearMap.comp p.toLinearMap) _
    rw [Submodule.map_comp]
  refine ⟨(P ⧸ I) ⧸ J, inferInstance, inferInstance, co_quot O P _ q hq, inferInstance, q, W2, h2,
    fun j => Nat.card {i // wt' i = j}, hq, fun s => ⟨s, rfl⟩, hpartq, ?_, ?_, ?_,
    ⟨τ', inferInstance, wt', _, hgr, fun j => rfl⟩, ?_⟩
  · rw [ho2]
    ext y
    rfl
  · intro k
    show p2 (p (g k)) = 0
    have : p (g k) = 0 := by
      show Ideal.Quotient.mk I (g k) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hI]
      exact Ideal.subset_span ⟨k, rfl⟩
    rw [this, map_zero]
  · intro δ hδ h0 y hy
    obtain ⟨δ', hδ'mem, hδ'⟩ := der_desc (W.origin h) g (fun k => (hgw k).2) p hp hpker x' hx' δ hδ h0
    rw [← hδ' y]
    have hJy : p y ∈ J := by
      have : p2 (p y) = 0 := hy
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    apply hdk δ' (by rw [ho1]; exact hδ'mem) (p y) hJy
  · intro j
    rw [← hn j]
    exact hn' j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.FgMapMk
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem fg_map_mk {O A S : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing S]
    [Algebra O S] (f : A →ₐ[O] S) (I : Ideal A) (hI : ∀ a, f a = 0 ↔ a ∈ I) (P : Submodule O A) (T : Submodule O S)
    (hT : T.FG) (hP : ∀ a ∈ P, f a ∈ T) : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).FG := by
  have hIf : ∀ a ∈ I, f a = 0 := fun a ha => (hI a).mpr ha
  let g : A ⧸ I →ₐ[O] S := Ideal.Quotient.liftₐ I f hIf
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hI a).mp hy
  haveI : IsNoetherian O T := isNoetherian_of_fg_of_noetherian T hT
  have hle : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).map g.toLinearMap ≤ T := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hP a ha
  exact Submodule.fg_of_fg_map_injective g.toLinearMap hg (isNoetherian_submodule.mp inferInstance _ hle)

theorem UpperTheory.V.GradeZeroInterpolatingElement.m2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → M2 M.gr M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hF
  obtain ⟨h1, -, h3⟩ := kerA D hD M
  have hs := spanMono D hD M hF 0
  have hfin := hF M.S M.ru M.pt
  have hT : (Subalgebra.toSubmodule (Algebra.adjoin c.O (mono M.ru.hom 0))).FG :=
    Module.Finite.iff_fg.1 hfin
  refine fg_map_mk (M.SS.val.comp M.toSS) _ (fun a => ?_) _ _ hT (fun a ha => ?_)
  · rw [← h1 a]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have h4 : (M.toSS a).1 ∈ M.sPart 0 := h3 0 a ha
    rw [hs] at h4
    exact Algebra.span_le_adjoin _ _ h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ (K : Type) [CommRing K] [Algebra c.O K] (ξ ξ' : M.SS →ₐ[c.O] K), M.rep ξ = M.rep ξ' → ξ = ξ' := by
  intro Ω _ _ _ l _ c D hD M h0 K _ _ ξ ξ' hrep
  have hent : ∀ g i j, ξ (M.ent g i j) = ξ' (M.ent g i j) := by
    intro g i j
    have := congrArg (fun r => r g i j) hrep
    simpa [Model.rep, mapRep, Model.rS, RingHom.mapMatrix_apply] using this
  let Q : Subalgebra c.O M.S := (AlgHom.equalizer ξ ξ').map M.SS.val
  have hQent : ∀ g i j, M.ru.hom g i j ∈ Q := by
    intro g i j
    exact ⟨M.ent g i j, hent g i j, rfl⟩
  have hQmono : ∀ w, mono M.ru.hom w ⊆ (Q : Set M.S) := by
    intro w y hy
    obtain ⟨L, -, rfl⟩ := hy
    apply Subalgebra.list_prod_mem
    intro z hz
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact hQent _ _ _
  have hle : (⨆ j, M.sPart j) ≤ Subalgebra.toSubmodule Q := by
    refine iSup_le fun w => ?_
    rw [spanMono D hD M h0 w, Submodule.span_le]
    exact hQmono w
  apply AlgHom.ext
  intro x
  have hx : (x : M.S) ∈ ⨆ j, M.sPart j := x.2
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLimit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem mem_gradedSub {O S X : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup X]
    (𝒜 : X → Submodule O S) [SetLike.GradedMonoid 𝒜] {j : X} {f : S} (hf : f ∈ 𝒜 j) : f ∈ gradedSub 𝒜 := by
  show f ∈ ⨆ i, 𝒜 i
  exact Submodule.mem_iSup_of_mem j hf

private theorem limit_graded {O S X K : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup X]
    [CommRing K] [Algebra O K] (𝒜 : X → Submodule O S) [SetLike.GradedMonoid 𝒜] (hI : iSupIndep 𝒜)
    (ξ : gradedSub 𝒜 →ₐ[O] K) (p : X →+ ℤ)
    (h : ∀ j f (hf : f ∈ 𝒜 j), p j < 0 → ξ ⟨f, mem_gradedSub 𝒜 hf⟩ = 0) :
    ∃ ξ₀ : gradedSub 𝒜 →ₐ[O] K, ∀ j f (hf : f ∈ 𝒜 j),
      ξ₀ ⟨f, mem_gradedSub 𝒜 hf⟩ = if p j = 0 then ξ ⟨f, mem_gradedSub 𝒜 hf⟩ else 0 := by
  classical
  let B := gradedSub 𝒜
  let Z : Set X := {j | p j = 0}
  let P0 : Submodule O B := Submodule.comap B.val.toLinearMap (⨆ j ∈ Z, 𝒜 j)
  let P1 : Submodule O B := Submodule.comap B.val.toLinearMap (⨆ j ∈ Zᶜ, 𝒜 j)
  have hdisj := hI.disjoint_biSup_biSup (s := Z) (t := Zᶜ) disjoint_compl_right
  have hc : IsCompl P0 P1 := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x h0 h1
      exact Subtype.ext (Submodule.disjoint_def.mp hdisj _ h0 h1)
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      have hle : (⨆ j, 𝒜 j) ≤ (⨆ j ∈ Z, 𝒜 j) ⊔ (⨆ j ∈ Zᶜ, 𝒜 j) := by
        refine iSup_le fun j => ?_
        by_cases hj : j ∈ Z
        · exact le_sup_of_le_left (le_biSup 𝒜 hj)
        · exact le_sup_of_le_right (le_biSup 𝒜 hj)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hle hx)
      have hsub : ∀ s : Set X, (⨆ j ∈ s, 𝒜 j) ≤ ⨆ j, 𝒜 j := fun s => iSup₂_le fun j _ => le_iSup 𝒜 j
      have haB : a ∈ B := hsub Z ha
      have hbB : b ∈ B := hsub Zᶜ hb
      exact Submodule.mem_sup.mpr ⟨⟨a, haB⟩, ha, ⟨b, hbB⟩, hb, Subtype.ext hab⟩
  let L : B →ₗ[O] K := ξ.toLinearMap ∘ₗ Submodule.projection P0 P1 hc
  have hform : ∀ j f (hf : f ∈ 𝒜 j),
      L ⟨f, mem_gradedSub 𝒜 hf⟩ = if p j = 0 then ξ ⟨f, mem_gradedSub 𝒜 hf⟩ else 0 := by
    intro j f hf
    split_ifs with hj
    · have hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P0 := (le_biSup 𝒜 (show j ∈ Z from hj)) hf
      show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _
      rw [Submodule.projection_apply_of_mem_left hc hm]
    · have hm : (⟨f, mem_gradedSub 𝒜 hf⟩ : B) ∈ P1 := (le_biSup 𝒜 (show j ∈ Zᶜ from hj)) hf
      show ξ (Submodule.projection P0 P1 hc ⟨f, mem_gradedSub 𝒜 hf⟩) = _
      have h0 := Submodule.projection_apply_right hc ⟨_, hm⟩
      rw [h0, map_zero]
  have hmul_h : ∀ j k f g (hf : f ∈ 𝒜 j) (hg : g ∈ 𝒜 k),
      L (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩) =
        L ⟨f, mem_gradedSub 𝒜 hf⟩ * L ⟨g, mem_gradedSub 𝒜 hg⟩ := by
    intro j k f g hf hg
    have hfg : f * g ∈ 𝒜 (j + k) := SetLike.GradedMul.mul_mem hf hg
    have e : (⟨f, mem_gradedSub 𝒜 hf⟩ * ⟨g, mem_gradedSub 𝒜 hg⟩ : B) = ⟨f * g, mem_gradedSub 𝒜 hfg⟩ := rfl
    have hm : ξ ⟨f * g, mem_gradedSub 𝒜 hfg⟩ = ξ ⟨f, mem_gradedSub 𝒜 hf⟩ * ξ ⟨g, mem_gradedSub 𝒜 hg⟩ := by
      rw [← map_mul]
      rfl
    have h1 := h j f hf
    have h2 := h k g hg
    rw [e, hform _ _ hfg, hform _ _ hf, hform _ _ hg, map_add p]
    by_cases hj : p j = 0 <;> by_cases hk : p k = 0
    · simp [hj, hk, hm]
    · have : p j + p k ≠ 0 := by omega
      simp [hj, hk, this]
    · have : p j + p k ≠ 0 := by omega
      simp [hj, hk, this]
    · by_cases hs : p j + p k = 0
      · simp only [hs, hj, hk, if_true, if_false, mul_zero, hm]
        rcases lt_or_gt_of_ne hj with hj' | hj'
        · rw [h1 hj', zero_mul]
        · rw [h2 (by omega), mul_zero]
      · simp [hs, hj, hk]
  have hmul : ∀ (x : S) (hx : x ∈ ⨆ j, 𝒜 j) (y : S) (hy : y ∈ ⨆ j, 𝒜 j),
      L ((⟨x, hx⟩ : B) * ⟨y, hy⟩) = L ⟨x, hx⟩ * L ⟨y, hy⟩ := by
    intro x hx y hy
    induction hx using Submodule.iSup_induction' with
    | mem j f hf =>
      induction hy using Submodule.iSup_induction' with
      | mem k g hg => exact hmul_h j k f g hf hg
      | zero =>
        change L ((⟨f, _⟩ : B) * 0) = L ⟨f, _⟩ * L 0
        simp
      | add a b ha hb iha ihb =>
        change L ((⟨f, _⟩ : B) * (⟨a, ha⟩ + ⟨b, hb⟩)) = L ⟨f, _⟩ * L (⟨a, ha⟩ + ⟨b, hb⟩)
        rw [mul_add, map_add, map_add, mul_add, iha, ihb]
    | zero =>
      change L ((0 : B) * ⟨y, hy⟩) = L 0 * L ⟨y, hy⟩
      simp
    | add a b ha hb iha ihb =>
      change L (((⟨a, ha⟩ : B) + ⟨b, hb⟩) * ⟨y, hy⟩) = L (⟨a, ha⟩ + ⟨b, hb⟩) * L ⟨y, hy⟩
      rw [add_mul, map_add, map_add, add_mul, iha, ihb]
  have hone : L 1 = 1 := by
    have h1 : (1 : S) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
    have e : (1 : B) = ⟨1, mem_gradedSub 𝒜 h1⟩ := rfl
    rw [e, hform _ _ h1, if_pos (map_zero p)]
    rw [← e, map_one]
  refine ⟨AlgHom.ofLinearMap L hone (fun x y => hmul x.1 x.2 y.1 y.2), ?_⟩
  intro j f hf
  exact hform j f hf

private theorem vanish_mono {O S K H : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    [Group H] (A : Subalgebra O S) (r : H →* M4 S) (hr : ∀ g i j, r g i j ∈ A) (ξ : A →ₐ[O] K)
    (p : ℤ × ℤ →+ ℤ) (h : ∀ g i j, p (wt i j) < 0 → ξ ⟨r g i j, hr g i j⟩ = 0) (w : ℤ × ℤ) (hw : p w < 0)
    (f : S) (hf : f ∈ Submodule.span O (mono r w)) (hA : f ∈ A) : ξ ⟨f, hA⟩ = 0 := by
  have hmemA : ∀ L : List (H × Fin 4 × Fin 4), (L.map (fun a => r a.1 a.2.1 a.2.2)).prod ∈ A := by
    intro L
    induction L with
    | nil => simpa using A.one_mem
    | cons a L ih => simpa using A.mul_mem (hr a.1 a.2.1 a.2.2) ih
  have hξL : ∀ L : List (H × Fin 4 × Fin 4), ξ ⟨_, hmemA L⟩ =
      (L.map (fun a => ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩)).prod := by
    intro L
    induction L with
    | nil =>
      have e : (⟨_, hmemA []⟩ : A) = 1 := Subtype.ext (by simp)
      rw [e, map_one]
      simp
    | cons a L ih =>
      have e : ξ ⟨_, hmemA (a :: L)⟩ = ξ ⟨r a.1 a.2.1 a.2.2, hr a.1 a.2.1 a.2.2⟩ * ξ ⟨_, hmemA L⟩ := by
        rw [← map_mul]
        apply congrArg ξ
        apply Subtype.ext
        simp
      rw [e, ih]
      simp
  have hspan : Submodule.span O (mono r w) ≤ Subalgebra.toSubmodule A := by
    rw [Submodule.span_le]
    rintro x ⟨L, -, rfl⟩
    exact hmemA L
  revert hA
  induction hf using Submodule.span_induction with
  | mem x hx =>
    intro hA
    obtain ⟨L, hL, rfl⟩ := hx
    refine (hξL L).trans ?_
    apply List.prod_eq_zero
    by_contra hne
    have hall : ∀ a ∈ L, 0 ≤ p (wt a.2.1 a.2.2) := by
      intro a ha
      by_contra hlt
      push_neg at hlt
      exact hne (List.mem_map.mpr ⟨a, ha, h a.1 a.2.1 a.2.2 hlt⟩)
    have hnn : 0 ≤ p w := by
      rw [← hL, map_list_sum, List.map_map]
      apply List.sum_nonneg
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact hall a ha
    omega
  | zero =>
    intro hA
    have e : (⟨0, hA⟩ : A) = 0 := rfl
    rw [e, map_zero]
  | add x y hx hy ihx ihy =>
    intro hA
    have e : (⟨x + y, hA⟩ : A) = ⟨x, hspan hx⟩ + ⟨y, hspan hy⟩ := rfl
    rw [e, map_add, ihx, ihy, add_zero]
  | smul a x hx ih =>
    intro hA
    have e : (⟨a • x, hA⟩ : A) = a • (⟨x, hspan hx⟩ : A) := rfl
    rw [e, map_smul, ih, smul_zero]

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptLimit :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ((∀ i j, lamW i < lamW j → ¬ Ge (M.rep ξ) i j) ∨ ∀ i j, lamW j < lamW i → ¬ Ge (M.rep ξ) i j) → ∃ ξ₀ : M.SS →ₐ[c.O] PadicAlgCl l, ∀ g i j, M.rep ξ₀ g i j = if lamW i = lamW j then M.rep ξ g i j else 0 := by
  intro Ω _ _ _ l _ c D hD M hF ξ hcase
  have hrep : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j,
      M.rep ζ g i j = ζ ⟨M.ru.hom g i j, M.sPart_le (M.entry_mem g i j)⟩ := by
    intro ζ g i j
    rfl
  obtain ⟨p, hp, hp0⟩ : ∃ p : ℤ × ℤ →+ ℤ, (∀ g i j, p (wt i j) < 0 → M.rep ξ g i j = 0) ∧
      ∀ i j, (p (wt i j) = 0 ↔ lamW i = lamW j) := by
    rcases hcase with hc | hc
    · refine ⟨AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩
      · intro g i j hlt
        have h1 : lamW i < lamW j := by
          simp only [wt, AddMonoidHom.coe_fst] at hlt
          omega
        have := hc i j h1
        simp only [Ge, not_exists, not_not] at this
        exact this g
      · intro i j
        simp only [wt, AddMonoidHom.coe_fst]
        constructor <;> intro h <;> omega
    · refine ⟨-AddMonoidHom.fst ℤ ℤ, ?_, ?_⟩
      · intro g i j hlt
        have h1 : lamW j < lamW i := by
          simp only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst] at hlt
          omega
        have := hc i j h1
        simp only [Ge, not_exists, not_not] at this
        exact this g
      · intro i j
        simp only [wt, AddMonoidHom.neg_apply, AddMonoidHom.coe_fst]
        constructor <;> intro h <;> omega
  obtain ⟨hI, -, -⟩ := sInternal D hD M
  have hvan : ∀ j f (hf : f ∈ M.sPart j), p j < 0 → ξ ⟨f, mem_gradedSub M.sPart hf⟩ = 0 := by
    intro j f hf hj
    have hf' : f ∈ Submodule.span c.O (mono M.ru.hom j) := by
      rw [← spanMono D hD M hF j]
      exact hf
    exact vanish_mono M.SS M.ru.hom (fun g i j => M.sPart_le (M.entry_mem g i j)) ξ p
      (fun g i j hlt => (hrep ξ g i j).symm.trans (hp g i j hlt)) j hj f hf' _
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : M.SS →ₐ[c.O] PadicAlgCl l, ∀ j f (hf : f ∈ M.sPart j),
      ξ₀ ⟨f, M.sPart_le hf⟩ = if p j = 0 then ξ ⟨f, M.sPart_le hf⟩ else 0 :=
    limit_graded M.sPart hI ξ p hvan
  refine ⟨ξ₀, fun g i j => ?_⟩
  rw [hrep, hrep, hξ₀ (wt i j) _ (M.entry_mem g i j)]
  by_cases hij : lamW i = lamW j
  · rw [if_pos ((hp0 i j).mpr hij), if_pos hij]
  · rw [if_neg (fun h => hij ((hp0 i j).mp h)), if_neg hij]
end

