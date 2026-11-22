import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
import Development.EtaleCohomology.EtaleSheaves.Bundle0041
import Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityEqLocallyConstantPowersSpectrum
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0002
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleLocalPrimitiveRootAndRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SchemeRootsOfUnityEqLocallyConstantPowers
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers :
    ∀ (X : Scheme.{0}) [IsAffine X] (q : ℕ) [NeZero q] (ζ : Γ(X, ⊤)), GoodRoot q ζ →
      (∀ g : LocallyConstant X (ZMod q), ∃ w : Γ(X, ⊤), w ^ q = 1 ∧ ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ w : Γ(X, ⊤), w ^ q = 1 → ∃ g : LocallyConstant X (ZMod q), ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ (a b : ZMod q) (x : X), x ∉ X.basicOpen (ζ ^ a.val - ζ ^ b.val) → a = b) ∧
      ∀ x : X, ∃ P : Ideal Γ(X, ⊤), ∀ f, f ∈ P ↔ x ∉ X.basicOpen f := by
  intro X _ q _ ζ hζ
  have hb : ∀ (x : X) (f : Γ(X, ⊤)), x ∉ X.basicOpen f ↔ f ∈ (X.toSpecΓ x).asIdeal := by
    intro x f
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact not_not
  let h := X.isoSpec.hom.homeomorph
  obtain ⟨h1, h2, h3⟩ := UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum Γ(X, ⊤) q ζ hζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨w, hwq, hw⟩ := h1 (LocallyConstant.comap ⟨h.symm, h.symm.continuous⟩ g)
    refine ⟨w, hwq, fun x => ?_⟩
    rw [hb]
    have hx := hw (h x)
    change w - ζ ^ (g (h.symm (h x))).val ∈ (h x).asIdeal at hx
    rw [h.symm_apply_apply] at hx
    exact hx
  · intro w hw
    obtain ⟨g, hg⟩ := h2 w hw
    refine ⟨LocallyConstant.comap ⟨h, h.continuous⟩ g, fun x => ?_⟩
    rw [hb]
    exact hg (h x)
  · intro a b x hx
    rw [hb] at hx
    exact h3 a b _ hx
  · intro x
    exact ⟨(X.toSpecΓ x).asIdeal, fun f => (hb x f).symm⟩

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexBotTotalModel
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ConstantCochains

variable {R : Type} [CommRing R] {E : Spc} {K : Cx R}

private theorem map_id' {p : ℕ} {U : Scheme.{0}} (z : Sx E p U) : Sx.map (𝟙 E) z = z := rfl

private def cst {U : Scheme.{0}} {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) : Sec (K.X b) U := e ▸ v

private theorem res_cst {V U : Scheme.{0}} (g : V ⟶ U) {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) :
    Sec.res g (cst e v) = cst e (Sec.res g v) := by
  subst e; rfl

private theorem cst_fam (x : (famDC (Sub.bot E) K 0).Tot) (p : ℕ) (U : Scheme.{0}) (z : Sx E p U)
    {s t : ℤ} (e : t = s) (e' : t + 0 = s + 0) :
    (show Fam (Sub.bot E) p (K.X (s + 0)) from x p s).1 U z =
      cst e' ((show Fam (Sub.bot E) p (K.X (t + 0)) from x p t).1 U z) := by
  subst e; rfl

private theorem exists_cochain (n : ℤ) (x : (famDC (Sub.bot E) K 0).Tot) :
    ∃ γ : Cochain ((chains R).obj E) K n, Comp (𝟙 E) γ x := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := E) (I := K) (n := n)
    (fun p s _ U z => cst (add_zero s) ((x p s).1 U z))
    (by
      intro p s h V U g z
      rw [res_cst, (x p s).2.1 V U g z])
  refine ⟨γ, ?_⟩
  intro p s h U z
  rw [map_id', hγ]
  exact cst_fam x p U z (add_zero s) (add_zero (s + 0))

private theorem eq_zero_of_comp {N : ℤ} (γ : Cochain ((chains R).obj E) K N)
    (h : Comp (𝟙 E) γ (0 : (famDC (Sub.bot E) K 0).Tot)) : γ = 0 := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := K) (n := N)).2.2.1 γ 0 fun p s hs U z => ?_
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 0 := ⟨s, (add_zero s).symm⟩
  have h1 := h p t hs U z
  rw [map_id'] at h1
  rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := K) (n := N)).1 γ γ p (t + 0) hs U z).2.2.1, ← h1]
  rfl

private theorem eq_of_comp {N : ℤ} (γ γ' : Cochain ((chains R).obj E) K N)
    (x : (famDC (Sub.bot E) K 0).Tot) (h : Comp (𝟙 E) γ x) (h' : Comp (𝟙 E) γ' x) : γ = γ' := by
  have h2 := (UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 N N (add_zero N)).2.2.2.1 γ γ' x x h h'
  rw [sub_self] at h2
  exact sub_eq_zero.1 (eq_zero_of_comp _ h2)

end UpperTheory.ConstantCochains

open UpperTheory.ConstantCochains in
theorem UpperTheory.supportDoubleComplex_bot_totalModel :
    ∀ (R : Type) [CommRing R] (E : Spc) (K : Cx R) (n : ℤ), TModel (famDC (Sub.bot E) K 0) n (HRel (E := E) (K := K) (n := n)) := by
  intro R _ E K n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have Ik := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 k k (add_zero k)
  have I1 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1) (k + 1) (add_zero _)
  have I2 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1 + 1) (k + 1 + 1) (add_zero _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ⟩ := exists_cochain (k + 1) x
    have h1 := I1.2.2.1 γ x hγ
    rw [hD] at h1
    have h0 := eq_zero_of_comp _ h1
    exact ⟨CohomologyClass.mk (Cocycle.mk γ _ rfl h0), Cocycle.mk γ _ rfl h0, rfl, hγ⟩
  · intro c
    obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
    obtain ⟨x, hx, hc⟩ := I1.1 γ (fun _ _ _ _ _ hm => False.elim hm)
    refine ⟨x, hx, ?_, γ, rfl, hc⟩
    have h1 := I1.2.2.1 γ x hc
    rw [Cocycle.δ_eq_zero] at h1
    have c00 : Comp (𝟙 E) (0 : Cochain ((chains R).obj E) K (k + 1 + 1))
        (0 : (famDC (Sub.bot E) K 0).Tot) := by
      intro p s h U z
      rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := K) (n := k + 1 + 1)).1 0 0 p _ h U _).2.2.1]
      rfl
    exact I2.2.1 0 _ 0 (I1.2.2.2.2 x hx) (fun _ _ _ => rfl) h1 c00
  · rintro x c x' c' ⟨γ, rfl, hγ⟩ ⟨γ', rfl, hγ'⟩
    exact ⟨γ - γ', CohomologyClass.mk_sub _ _, I1.2.2.2.1 _ _ _ _ hγ hγ'⟩
  · rintro x c hx ⟨γ, rfl, hγ⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ k rfl, add_sub_cancel_right]
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨y, hy, hyβ⟩ := Ik.1 β (fun _ _ _ _ _ hm => False.elim hm)
      refine ⟨y, hy, ?_⟩
      have h1 := Ik.2.2.1 β y hyβ
      rw [hβ] at h1
      exact I1.2.1 _ _ _ (Ik.2.2.2.2 y hy) hx h1 hγ
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ⟩ := exists_cochain k y
      exact ⟨β, eq_of_comp _ _ _ (Ik.2.2.1 β y hβ) hγ⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistGeneratorOfPrimitiveRootAndRootsEtaleLo
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

theorem UpperTheory.tateTwist_generator_of_primitiveRoot_and_roots_etaleLocal :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}), (∀ ζ : GlobalTheory.EtC.Prim q Γ(U, ⊤), Gen Scheme.etaleTopology q (GlobalTheory.EtC.tw q i).obj (GlobalTheory.EtC.twGen i ζ)) ∧ (UpperTheory.Et.Inv q U → LocT Scheme.etaleTopology U fun V _ => Nonempty (GlobalTheory.EtC.Prim q Γ(V, ⊤))) := by
  intro q _ i U
  obtain ⟨-, h2, h3, h4, -⟩ := UpperTheory.Cb.tateTwist_sections_locally_generated q i
  refine ⟨fun ζ => ⟨?_, ?_, ?_⟩, fun hq => (UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq⟩
  · have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext _ _ (ZMod.natCast_self q)
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q, h0, zero_smul]
  · intro V k c hV hc
    haveI := hV
    refine h3 V (ζ.map k.appTop.hom) c ?_
    rw [← h4 V U k ζ]
    exact hc
  · intro V k y
    obtain ⟨S, hS, h⟩ := h2 V (ζ.map k.appTop.hom) y
    refine ⟨S, hS, fun W g hg => ?_⟩
    obtain ⟨c, hc⟩ := h W g hg
    refine ⟨c, hc.trans ?_⟩
    have e : GlobalTheory.EtC.twGen i ((ζ.map k.appTop.hom).map g.appTop.hom) =
        GlobalTheory.EtC.Sec.res (g ≫ k) (GlobalTheory.EtC.twGen i ζ) := by
      rw [← h4 W V g, ← h4 V U k]
      simp [GlobalTheory.EtC.Sec.res]
    rw [e]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm, mul_nsmul, tw_q_nsmul, add_zero]

private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have hq : 1 ≤ q := NeZero.pos q
  have h1 : (q - 1) * c' + c' = q * c' := by
    have : (q - 1) * c' + c' = ((q - 1) + 1) * c' := by ring
    rw [this, Nat.sub_add_cancel hq]
  have h0 : (c + (q - 1) * c') • twGen i ζ = 0 := by
    rw [add_nsmul, h, ← add_nsmul, add_comm, h1, mul_comm, mul_nsmul, tw_q_nsmul]
  obtain ⟨k, hk⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have h2 : c + q * c' = c' + q * k := by
    rw [← hk, ← h1]
    ring
  calc c % q = (c + q * c') % q := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (c' + q * k) % q := by rw [h2]
    _ = c' % q := Nat.add_mul_mod_self_left _ _ _

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem res_gen {q : ℕ} [NeZero q] {i : ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (ζ : Prim q Γ(U, ⊤)) :
    Sec.res k (twGen i (ζ.map g.appTop.hom)) = twGen i (ζ.map (k ≫ g).appTop.hom) := by
  rw [(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1]
  congr 1

theorem UpperTheory.twisted_section_eq_nsmul_generator_of_connected :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) [ConnectedSpace X] (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X), ∃ c : ℕ, y = c • twGen i ζ := by
  intro q _ i X _ ζ y
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y
  have hpts := (loc_iff_etale_affine_points X (fun V g => S.arrows g)
    (fun V W g k h => S.downward_closed h k)).1 ⟨S, hS, fun _ _ h => h⟩
  choose V g hA hE hx hS' using hpts
  choose c hc using fun x => hP (V x) (g x) (hS' x)
  have hlc : IsLocallyConstant (fun x => c x % q) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    haveI := hE x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, ?_⟩
    rintro x' ⟨v, hv⟩
    obtain ⟨v', hv'⟩ := hx x'
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g x) (g := g x') v v' (hv.trans hv'.symm)
    haveI : Nonempty ↥(pullback (g x) (g x')) := ⟨z⟩
    have e1 := congrArg (Sec.res (pullback.fst (g x) (g x'))) (hc x)
    have e2 := congrArg (Sec.res (pullback.snd (g x) (g x'))) (hc x')
    rw [← res_comp, res_nsmul, res_gen] at e1 e2
    rw [pullback.condition] at e1
    exact (mod_eq_of_nsmul_eq _ (e1.symm.trans e2)).symm
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, c x % q = c x0 % q := fun x => hlc.apply_eq_of_preconnectedSpace x x0
  refine ⟨c x0, (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X _ ?_).2 fun x => ⟨V x, g x, hA x, hE x, hx x, ?_⟩
  · intro V W g k h
    rw [res_comp, res_comp, h]
  · rw [hc, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1, tw_nsmul_mod, hconst x, ← tw_nsmul_mod]
end

