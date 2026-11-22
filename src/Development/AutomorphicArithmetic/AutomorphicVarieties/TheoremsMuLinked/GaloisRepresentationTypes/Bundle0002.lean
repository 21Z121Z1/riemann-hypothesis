import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.RegDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.PolNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.OpOfProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.TpSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0005

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AutKQ
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Th.autKQ :
    Af.HypothesesH → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ), Continuous r → IsAutQ ι r → (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → AutP ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) := by
  intro hP K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r wt hc hr ⟨θ, hθ, hd⟩ hirr
  obtain ⟨P, hreg, hA⟩ := hr hc K hK hirr
  obtain ⟨χ, -, hpol, -⟩ := UpperTheory.V.Z.Bc.polK hP.toClassicalTheorems K hK n hn l Ω ι r wt θ P hθ hd hA
  exact ⟨P, hreg, ⟨χ, hpol⟩, hA⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CoreOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl

private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)

theorem UpperTheory.V.Th.core_of :
    Th.OrdVan2 → W.PhiAll → Th.Core := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 _).1 (by simpa using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.HasOp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Th.hasOp :
    HasOp := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b hb T Q
  refine ⟨2 * n.factorial, ?_⟩
  · skip
    intro N
    have hl : ∀ j, ((l : ℕ) : 𝓞 L) ∉ (Q.w N j).asIdeal := by
      intro j hj
      apply Q.v_not N j
      left
      have h1 := (Q.B_w N j (l : 𝓞 L)).2 hj
      refine (Q.B_v N j (l : 𝓞 (Lp L))).1 ?_
      simpa using h1
    obtain ⟨A, ι, hι⟩ := hb (Q.V N) (homComp (Q.e N) (T.h N)) T.q (Q.v N) (Q.w N) (Q.B N) (Q.e_h N) (Q.v_inj N) (Q.v_not N)
      (Q.S_eq N) (Q.B_w N) (Q.B_v N) (Q.split N)
    have hd := fun j => locData hP l L Ω (Q.B N j) (Q.w N j) (Q.B_w N j) (hl j) (Q.fr N j) (Q.τ N j) (Q.fr_dec N j)
      (Q.fr_frob N j) (Q.τ_gen N j)
    choose hq x δ hx hδ hrel using hd
    have hNq : T.Nq N = qj (Q.w N) := funext fun j => (Q.Nq N j).trans (hq j).symm
    have hok : LocOk A x δ (fun j => (Q.V N).pr (Q.fr N j)) (fun j => (Q.V N).pr (Q.τ N j)) :=
      ⟨ι, hι, fun y j => hrel j n ι (y.rep.comp (Q.V N).pr) (y.σ j) (y.lg j (Q.B N j) (Q.B_w N j))⟩
    obtain ⟨A1, h1⟩ := opOfX hP l L Ω s V0 O n r B J _ b (Q.V N) _ T.q (Q.w N) A x δ hl hx hδ _ _ N hok
      (fun j => by rw [← hNq]; exact T.Nq_mod N j)
    obtain ⟨A2, h2⟩ := opTransportX l _ _ O n _ B.B _ J _ b _ _ (Q.e N) _ (T.h N) T.q N A1 _ _ _ _ (Q.e_inj N) (fun _ => rfl) h1
    have e1 : T.ph N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.fr N j)) := funext (Q.ph N)
    have e2 : T.ta N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.τ N j)) := funext (Q.ta N)
    rw [hNq, e1, e2]
    exact ⟨A2, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapRingHomSingleMulPartialCharpoly
section
open IsLocalRing Filter UpperTheory.V UpperTheory.V.Th UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev

private theorem cnt (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (c : O) (hc : c ≠ 0) (D0 C : ℕ) : ∃ m : ℕ, ∀ (ι : Type) [Fintype ι] (Y : Type) [AddCommGroup Y] [Module O Y]
      (Φ : (ι → O) →ₗ[O] Y) (S : Set Y), Fintype.card ι = D0 + 1 →
      (∀ t, Φ t = 0 → ∀ a, c * t a ∈ maximalIdeal O ^ m) → (∀ t, Φ t ∈ S) → S.Finite →
      ¬ S.ncard ≤ Nat.card (ResidueField O) ^ (m * D0 + C) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨v + (v * D0 + C + 1), fun ι _ Y _ _ Φ S hι hker hS hfin hle => ?_⟩
  set k := v * D0 + C + 1 with hk
  have hcard : Nat.card (O ⧸ maximalIdeal O ^ k) = Nat.card (ResidueField O) ^ k :=
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O)
  choose s hs using Ideal.Quotient.mk_surjective (I := maximalIdeal O ^ k)
  let f : (ι → O ⧸ maximalIdeal O ^ k) → S := fun t => ⟨Φ fun a => s (t a), hS _⟩
  have hf : Function.Injective f := fun t t' h => by
    have h1 : Φ ((fun a => s (t a)) - fun a => s (t' a)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val h
    funext a
    have h2 := hker _ h1 a
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_add, mul_assoc,
      Units.dvd_mul_left, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)] at h2
    rw [← hs (t a), ← hs (t' a), Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact h2
  haveI := hfin.to_subtype
  have h3 := (Nat.card_le_card_of_injective f hf).trans (le_of_eq_of_le (Nat.card_coe_set_eq S) hle)
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := ι), hι, ← pow_mul,
    Nat.pow_le_pow_iff_right Finite.one_lt_card] at h3
  nlinarith

section Tr

variable {n : ℕ} {R G : Type} [CommRing R] [Group G]

private theorem tr_lin (D : GDet n R G) (hn : 1 ≤ n) : ∃ t : MonoidAlgebra R G →ₗ[R] R, ∀ z, D.tr z = t z := by
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  exact ⟨t, fun z => ((UpperTheory.V.CA.d_toDet D z).2.2.1.symm.trans (ht z).symm)⟩

private theorem comap_tr {H : Type} [Group H] (D : GDet n R H) (φ : G →* H)
    (z : MonoidAlgebra R G) : (D.comap φ).tr z = D.tr (MonoidAlgebra.mapDomainRingHom R φ z) := by
  have hc : (D.comap φ).chi z = D.chi (MonoidAlgebra.mapDomainRingHom R φ z) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g r => simp
  simp only [GDet.tr, GDet.lam, hc]

private theorem map_tr {S : Type} [CommRing S] (D : GDet n R G) (f : R →+* S) (z : MonoidAlgebra R G) :
    f (D.tr z) = (D.map f).tr (MonoidAlgebra.mapRingHom G f z) :=
  (((UpperTheory.V.CA.d_gmap D).2.2.1 f z).2 1).symm

private theorem ofRep_comap' {H : Type} [Group H] (ρ : G →* Matrix (Fin n) (Fin n) R) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  ext B _ _ z
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ z)).det = (GDet.repAlg (ρ.comp φ) B z).det
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem mapRingHom_single_mul_partial_charpoly {S : Type} [CommRing S] (f : R →+* S) (E : ℕ) (ph ta : G) (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra.mapRingHom G f (twoPowerModulus E ph ta u i 0) = twoPowerModulus E ph ta (fun k => f (u k)) i 0 := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (f c) := fun g c => by simp
  simp only [twoPowerModulus, map_mul, map_pow, map_sub, map_one, map_list_prod, List.map_ofFn, hs, map_zero]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem mapDomain_partial_charpoly_power_zero {H : Type} [Group H] (φ : G →* H) (E : ℕ) (ph ta : G) (u : Fin n → R) (i : Fin n)
    (h : φ ta = 1) : MonoidAlgebra.mapDomainRingHom R φ (twoPowerModulus E ph ta u i 0) = 0 := by
  have hs : MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single ta 1) = 1 := by
    simp [h, MonoidAlgebra.one_def]
  simp only [twoPowerModulus, map_mul, map_sub, map_one, hs, MonoidAlgebra.single_zero, map_zero, sub_self, mul_zero]

private theorem kill_tr {O X : Type} [CommRing O] [Algebra O R] [AddCommGroup X] [Module O X] (D : GDet n R G)
    (hn : 1 ≤ n) (δ : R →ₗ[O] X) (h : ∀ g, δ (D.tr (MonoidAlgebra.single g 1)) = 0) (z : MonoidAlgebra O G) :
    δ (D.tr (MonoidAlgebra.mapRingHom G (algebraMap O R) z)) = 0 := by
  obtain ⟨t, ht⟩ := tr_lin D hn
  simp only [ht] at h ⊢
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single g a =>
    have : MonoidAlgebra.mapRingHom G (algebraMap O R) (MonoidAlgebra.single g a) =
        algebraMap O R a • MonoidAlgebra.single g (1 : R) := by
      rw [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, algebraMap_smul, map_smul, h, smul_zero]

end Tr

section Der

variable {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] {x : R →ₐ[O] O}

private theorem der_one {δ : R →ₗ[O] X} (h : IsDer x δ) : δ 1 = 0 := by
  have := h 1 1
  simpa using this

private theorem der_sum {ι : Type} [Fintype ι] (d : ι → R →ₗ[O] X) (h : ∀ a, IsDer x (d a)) (t : ι → O) :
    IsDer x (∑ a, t a • d a) := fun a b => by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, h _ a b, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul, mul_comm]

private theorem der_smul {δ : R →ₗ[O] X} (h : IsDer x δ) (c : O) : IsDer x (c • δ) := fun a b => by
  simp only [LinearMap.smul_apply, h a b, smul_add, smul_smul, mul_comm]

private theorem der_wt {δ : R →ₗ[O] X} (h : IsDer x δ) (c : O) (a : R) : δ (algebraMap O R c * a - 1) = c • δ a := by
  rw [map_sub, der_one h, sub_zero, ← Algebra.smul_def, map_smul]

end Der

theorem UpperTheory.V.Th.count :
    Count := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D b y x al hl hn had ⟨E, hA⟩ hgen hu hJ hEt hPL hEig ⟨C, hB⟩ δ0 hδ0 hw g0
  classical
  by_contra hd
  haveI : Finite (ResidueField O) := IsCoef.finite
  choose A hA using hA
  obtain ⟨c1, hc1, h1⟩ := coc l L G0 n O y hl hn
  obtain ⟨c2, hc2, h2⟩ := trPsi l L G0 n O y hn
  obtain ⟨c3, hc3, h3⟩ := split l L G0 T n O r B u J D b y x al E hn hgen hu hJ hEt hPL hEig
  set d := δ0 (u.D.tr (MonoidAlgebra.single g0 1)) with hdd
  obtain ⟨m, hm⟩ := cnt O (c1 * c2 * c3 * d) (mul_ne_zero (mul_ne_zero (mul_ne_zero hc1 hc2) hc3) hd) (D + n * T.q) C
  obtain ⟨N, ⟨hfin, hle⟩, h3N⟩ := ((hB m).and (h3 m)).exists
  obtain ⟨α, hα⟩ := h3N (A N) (hA N)
  clear hA
  generalize A N = A at hα
  choose δ hδ hδw hδq using hα
  have hIp : ∀ w, A.rN.Ip w = (T.GN N).frame.Iu w := fun w => by
    refine inf_eq_left.2 (le_iInf fun i => ?_)
    rintro _ ⟨g, hg, rfl⟩
    have e : (T.h N).p₀ ((T.GN N).φu w g) = G0.φu w g := Subtype.ext ((T.h N).φu w g)
    have hm : G0.φu w g ∈ r.Ip w := by
      rw [had.2 w]
      exact ⟨g, hg, rfl⟩
    rw [MonoidHom.mem_ker, A.compat.1 i, MonoidHom.comp_apply, e]
    exact (Subgroup.mem_iInf.1 hm.2) i
  have hmaps : A.p.Maps (x.comp A.β).toRingHom (GDet.ofRep (mat (y.ρ.comp (T.h N).p₀))) y.ψ := by
    refine ⟨?_, fun v i => ?_⟩
    · have e1 : A.p.D.map (x.comp A.β).toRingHom = (A.p.D.map A.β.toRingHom).map x.toRingHom := rfl
      have e2 : (u.D.comap (T.h N).p₀).map x.toRingHom = (u.D.map x.toRingHom).comap (T.h N).p₀ := rfl
      rw [e1, A.β_pair.1, e2, hu.1, ofRep_comap']
      rfl
    · rw [← hu.2 v i, ← A.β_pair.2 v i]
      rfl
  have hβtr : ∀ z, A.β (A.p.D.tr z) =
      u.D.tr (MonoidAlgebra.mapDomainRingHom B (T.h N).p₀ (MonoidAlgebra.mapRingHom _ A.β.toRingHom z)) := fun z => by
    rw [← comap_tr, ← A.β_pair.1]
    exact map_tr A.p.D A.β.toRingHom z
  let δs : A.R →ₗ[O] Om O m := Algebra.linearMap O (Om O m) ∘ₗ δ0 ∘ₗ A.β.toLinearMap
  have hδs_apply : ∀ a, δs a = algebraMap O (Om O m) (δ0 (A.β a)) := fun _ => rfl
  have hδs : IsDer (x.comp A.β) δs := fun a a' => by
    simp only [hδs_apply, map_mul, hδ0 _ _, map_add, smul_eq_mul, AlgHom.comp_apply, Algebra.smul_def]
  let ι := Option (Fin D ⊕ Fin T.q × Fin n)
  let e : ι → A.R →ₗ[O] Om O m := fun a => a.elim δs δ
  have he : ∀ a, IsDer (x.comp A.β) (e a) := fun a => by
    cases a
    · exact hδs
    · exact hδ _
  let Φ : (ι → O) →ₗ[O] ((T.GN N).G₀ → Om O m) :=
    Fintype.linearCombination O fun a g => c1 • e a (A.p.D.tr (MonoidAlgebra.single g 1))
  have hΦ : ∀ t g, Φ t g = c1 • (∑ a, t a • e a) (A.p.D.tr (MonoidAlgebra.single g 1)) := fun t g => by
    simp only [Φ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, Finset.smul_sum, smul_comm c1]
  have hev : ∀ (t : ι → O) z, (∑ a, t a • e a) z = t none • δs z + ∑ a, t (some a) • δ a z := fun t z => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Fintype.sum_option _
  have hmem : ∀ a : O, a • (1 : Om O m) = 0 ↔ a ∈ maximalIdeal O ^ m := fun a => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Ideal.Quotient.eq_zero_iff_mem
  refine hm ι _ Φ _ (by simp [ι, mul_comm]) (fun t ht => ?_) (fun t => ?_) hfin hle
  swap
  · obtain ⟨z, hz, hz'⟩ := h1 _ (T.h N) A.rN A.R A.p _ hIp hmaps m _ (der_sum e he t)
    exact ⟨z, hz, funext fun g => (hz' g).trans (hΦ t g).symm⟩
  have hk : ∀ g, (c1 • ∑ a, t a • e a) (A.p.D.tr (MonoidAlgebra.single g 1)) = 0 := fun g =>
    (hΦ t g).symm.trans (congrFun ht g)
  have hder := der_smul (der_sum e he t) c1
  have hsome : ∀ a, (c1 * c2 * c3 * t (some a)) • (1 : Om O m) = 0 := by
    rintro (k | ⟨j, i⟩)
    · have k1 := h2 _ (T.h N) A.rN A.R A.p _ hmaps _ _ hder hk (b.wt.v k) (b.wt.i k) (b.wt.γ k)
      have k2 : c2 • (c1 • ∑ a, t a • e a) (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = 0 := by
        rw [A.segmentWeightExponent, der_wt hder, smul_comm, k1, smul_zero]
      have k3 : δs (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = 0 := by
        have k4 : A.β (A.p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : A.Rˣ) = (u.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : Bˣ) := by
          rw [← A.β_pair.2]
          rfl
        rw [A.segmentWeightExponent, der_wt hδs, hδs_apply, k4, hw, map_zero, smul_zero]
      rw [LinearMap.smul_apply, hev, k3] at k2
      simp only [hδw, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at k2
      simp only [Algebra.algebraMap_eq_smul_one, smul_smul] at k2
      rw [← k2]
      congr 1
      ring
    · have k1 := kill_tr A.p.D hn _ hk (twoPowerModulus E (T.ph N j) (T.ta N j) (α j) i 0)
      rw [mapRingHom_single_mul_partial_charpoly] at k1
      have k3 : δs (A.p.D.tr (twoPowerModulus E (T.ph N j) (T.ta N j) (fun k => algebraMap O A.R (α j k)) i 0)) = 0 := by
        obtain ⟨τ, hτ⟩ := tr_lin u.D hn
        rw [hδs_apply, hβtr, mapRingHom_single_mul_partial_charpoly, mapDomain_partial_charpoly_power_zero _ _ _ _ _ _ (Subtype.ext (T.ta_ker N j)), hτ, map_zero, map_zero, map_zero]
      rw [LinearMap.smul_apply, hev, k3] at k1
      simp only [hδq, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at k1
      simp only [Algebra.algebraMap_eq_smul_one, smul_smul] at k1
      have : c1 * c2 * c3 * t (some (.inr (j, i))) = c2 * (c1 * (t (some (.inr (j, i))) * c3)) := by ring
      rw [this, mul_smul, k1, smul_zero]
  rintro (_ | a)
  · obtain ⟨g', hg'⟩ := (T.h N).surj g0
    have hη : g' ∈ (T.GN N).η.ker := by
      rw [MonoidHom.mem_ker, ← (T.h N).η, hg']
      exact g0.2
    have e0 : (T.h N).p₀ ⟨g', hη⟩ = g0 := Subtype.ext hg'
    have k1 := hk ⟨g', hη⟩
    have k3 : δs (A.p.D.tr (MonoidAlgebra.single ⟨g', hη⟩ 1)) = d • (1 : Om O m) := by
      rw [hδs_apply, hβtr, MonoidAlgebra.mapRingHom_single, map_one, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, e0, Algebra.algebraMap_eq_smul_one]
    rw [LinearMap.smul_apply, hev, k3] at k1
    have k4 := congrArg (fun w => (c2 * c3) • w) k1
    have k5 : ∀ a (w : Om O m), (c2 * c3) • c1 • t (some a) • w = 0 := fun a w => by
      have : (c2 * c3) • c1 • t (some a) • w = ((c1 * c2 * c3 * t (some a)) • (1 : Om O m)) * w := by
        rw [smul_mul_assoc, one_mul, smul_smul, smul_smul]
        congr 1
        ring
      rw [this, hsome, zero_mul]
    simp only [smul_add, Finset.smul_sum, k5, Finset.sum_const_zero, add_zero, smul_zero] at k4
    rw [← hmem, ← k4]
    simp only [smul_smul]
    congr 1
    ring
  · rw [← hmem]
    have : c1 * c2 * c3 * d * t (some a) = d * (c1 * c2 * c3 * t (some a)) := by ring
    rw [this, mul_smul, hsome, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧
      (∀ s ∈ Dec (F := F) A, g⁻¹ * s * g ∈ Dec (F := F) B) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  have hD' : ∀ s ∈ Dec (F := F) (g • B), g⁻¹ * s * g ∈ Dec (F := F) B := fun s hs => by
    have h1 : s • g • B = g • B := hs
    show (g⁻¹ * s * g) • B = B
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  refine ⟨B, g, hB, hD', hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

private theorem flag_move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ (B : ValuationSubring Ω) (d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A)), IsPlaceOver B w ∧
      FlagAt M m (r.comp (res F Ω K)) B (fun i => (κ i).comp d) ∧
      (∀ s, cycBar F Ω l (d s) = cycBar K Ω l s) ∧
      (Dec (F := F) B ≤ (res F Ω K).range → Function.Surjective d) := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hκ⟩ := hκ
  obtain ⟨B, g, hB, hD', hD, hI⟩ := move w hA
  let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  refine ⟨B, d, hB, ⟨fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs,
    ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩, fun s => ?_, fun H s => ?_⟩
  · rw [MonoidHom.comp_apply, rep_conj]
    exact hP (d s)
  · have h := hκ i (d s) (hI s hs)
    rw [hd, char_conj, char_conj] at h
    exact h
  · rw [hd, char_conj]
    rfl
  · obtain ⟨t, ht⟩ := H (hD' s s.2)
    have htD : t ∈ Dec (F := K) B := by
      have h1 : res F Ω K t • B = B := by
        rw [ht]
        exact hD' s s.2
      exact h1
    refine ⟨⟨t, htD⟩, Subtype.ext ?_⟩
    rw [hd]
    show g * res F Ω K t * g⁻¹ = s
    rw [ht]
    group

end

theorem UpperTheory.V.Th.unlRes :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → ((∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω).range) → Unl l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) ∧ ((∀ i j, m i ≠ m j + 1) → Af.Level l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) := by
  intro K Ω _ _ _ _ _ _ _ l _ n M m r hM
  refine ⟨fun hdec H w hw => ?_, fun hm H w hw => ?_⟩
  · obtain ⟨A, hA, κ, hκ, hu⟩ := H (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, hc, hs⟩ := flag_move w hA hκ
    have hv : B.valuation (l : Ω) < 1 := by
      simpa using (hB _).2 hw
    refine ⟨B, hB, _, hF, fun i j e => hu i j (MonoidHom.ext fun s => ?_)⟩
    obtain ⟨t, rfl⟩ := hs (hdec B hv) s
    have h1 := DFunLike.congr_fun e t
    change κ i (d t) = κ j (d t) * cycBar K Ω l t at h1
    change κ i (d t) = κ j (d t) * cycBar ℚ Ω l (d t)
    rw [hc, h1]
  · obtain ⟨A, hA, κ, hκ⟩ := (Lev.LevelF.of_level H).above (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, -, -⟩ := flag_move w hA hκ
    exact ⟨B, hB, _, hF, Lev.unlGap K Ω l n M hM m _ w hw B hB _ hF hm⟩
end

