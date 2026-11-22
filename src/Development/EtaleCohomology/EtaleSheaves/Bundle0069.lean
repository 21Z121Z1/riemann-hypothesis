import Development.EtaleCohomology.EtaleSheaves.Bundle0062
import Development.EtaleCohomology.EtaleSheaves.Bundle0059
import Development.EtaleCohomology.EtaleSheaves.Bundle0061

-- bundled from Development.EtaleCohomology.EtaleSheaves.ResSmulGen
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.MulPf LateralTheory.E.TwistTrivial

namespace LateralTheory.E.GenPf

theorem field_log {q : ℕ} {K : Type} [Field K] (ζ ξ : Prim q K) :
    ∃! a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  haveI : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  haveI : NeZero q := NeZero.of_neZero_natCast K
  have hp : ∀ η : Prim q K, IsPrimitiveRoot η.1 q := fun η => by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    exact η.2.2
  obtain ⟨i, hi, hc, he⟩ := (hp ζ).isPrimitiveRoot_iff.1 (hp ξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_, fun b hb => ?_⟩
  · simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]
  · apply Units.ext
    have := (hp ζ).pow_inj (ZMod.val_lt (b : ZMod q)) hi (hb.symm.trans he.symm)
    rw [ZMod.coe_unitOfCoprime, ← this, ZMod.natCast_zmod_val]

theorem field_pow {q : ℕ} {K : Type} [Field K] (ζ : Prim q K) (a b : ZMod q) :
    ζ.1 ^ (a * b).val = (ζ.1 ^ a.val) ^ b.val := by
  haveI : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  haveI : NeZero q := NeZero.of_neZero_natCast K
  have hp : IsPrimitiveRoot ζ.1 q := by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    exact ζ.2.2
  rw [ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod _ hp.pow_eq_one]

theorem field_ann {q : ℕ} (j : ℤ) {K : Type} [Field K] (ζ : Prim q K) (c : ULift.{1} (ZMod q))
    (h : Finsupp.single ζ c ∈ twRel q j K) : c = 0 := by
  choose lg hlg hu using fun ξ => field_log ζ ξ
  let φ : (Prim q K →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
    Finsupp.linearCombination _ (fun ξ => ULift.up ((lg ξ ^ j : (ZMod q)ˣ) : ZMod q))
  have hk : twRel q j K ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨η, ξ, a, hξ, rfl⟩
    have e : lg η * a = lg ξ := hu ξ _ (by
      show ξ.1 = ζ.1 ^ ((lg η * a : (ZMod q)ˣ) : ZMod q).val
      rw [Units.val_mul, field_pow, ← hlg η, hξ])
    show φ _ = 0
    rw [map_sub]
    simp only [φ, Finsupp.linearCombination_single, ← e, one_smul, smul_eq_mul]
    rw [sub_eq_zero, mul_zpow]
    apply ULift.ext
    simp only [ULift.mul_down, Units.val_mul, ULift.one_down]
    ring
  have h1 : lg ζ = 1 := by
    haveI : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
    haveI : NeZero q := NeZero.of_neZero_natCast K
    have e : lg ζ * lg ζ = lg ζ := hu ζ _ (by
      show ζ.1 = ζ.1 ^ ((lg ζ * lg ζ : (ZMod q)ˣ) : ZMod q).val
      rw [Units.val_mul, field_pow, ← hlg ζ, ← hlg ζ])
    simpa using e
  have := hk h
  simp only [LinearMap.mem_ker, φ, Finsupp.linearCombination_single, h1, one_zpow, smul_eq_mul] at this
  exact (mul_one c).symm.trans this

theorem ring_ann {q : ℕ} (j : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ULift.{1} (ZMod q))
    (h : Finsupp.single ζ c ∈ twRel q j A) : c = 0 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field M
  have := twRel_le q j (Ideal.Quotient.mk M) h
  rw [Submodule.mem_comap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at this
  exact field_ann j _ c this

theorem ann {q : ℕ} (j l : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (c : ULift.{1} (ZMod q))
    (h : c • twGen j ζ = 0) : c • twGen l ζ = 0 := by
  have h0 : ofRings.sec (twF q j) X (Submodule.Quotient.mk (Finsupp.single ζ c) : (twF q j).obj Γ(X, ⊤)) =
      ofRings.sec (twF q j) X 0 := by
    rw [sec_single, h]
    exact (map_zero _).symm
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j))
    (X := op X) _ _ h0
  refine sep _ hS _ _ (fun Y f hf => ?_)
  have hf' : (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.appTop.hom) (Finsupp.single ζ c)) :
      (twF q j).obj Γ(Y, ⊤)) = 0 := Eq.trans hf (map_zero _)
  rw [Finsupp.mapDomain_single] at hf'
  by_cases hY : Nonempty Y
  · haveI : Nontrivial Γ(Y, ⊤) := by
      haveI : Nonempty (⊤ : Y.Opens) := hY.elim fun y => ⟨⟨y, trivial⟩⟩
      infer_instance
    have hc := ring_ann j _ c ((Submodule.Quotient.mk_eq_zero _).1 hf')
    rw [hc, zero_smul]
  · haveI : IsEmpty Y := not_nonempty_iff.1 hY
    exact sep ⊥ (by exact Scheme.bot_mem_grothendieckTopology Y) _ _ (fun _ _ hg => hg.elim)

theorem res_comp {q : ℕ} {j : ℤ} {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (f : Y ⟶ X) (x : Sec (tw q j) X) :
    Sec.res (h ≫ f) x = Sec.res h (Sec.res f x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]

theorem res_smul_gen {q : ℕ} {j : ℤ} {X Y : Scheme.{0}} (f : Y ⟶ X) (ζ : Prim q Γ(X, ⊤)) (c : ULift.{1} (ZMod q)) :
    Sec.res f (c • twGen j ζ) = c • twGen j (ζ.map f.appTop.hom) := by
  rw [← genRes]
  exact map_smul _ _ _

theorem ann2 {q : ℕ} (j l : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (c d : ULift.{1} (ZMod q))
    (h : c • twGen j ζ = d • twGen j ζ) : c • twGen l ζ = d • twGen l ζ := by
  rw [← sub_eq_zero, ← sub_smul] at h ⊢
  exact ann j l ζ _ h

theorem wd (hR : RootPow) {q : ℕ} {j k l : ℤ} (h : j + k = l) {X : Scheme.{0}} (ζ ξ : Prim q Γ(X, ⊤))
    (c d c' d' : ULift.{1} (ZMod q)) (h1 : c • twGen j ζ = c' • twGen j ξ) (h2 : d • twGen k ζ = d' • twGen k ξ) :
    (c * d) • twGen l ζ = (c' * d') • twGen l ξ := by
  obtain ⟨S, hS, hp⟩ := hR q X ζ {ξ}
  refine sep S hS _ _ (fun Y f hf => ?_)
  obtain ⟨a, ha⟩ := hp f hf ξ (Finset.mem_singleton_self _)
  have e1 := congrArg (Sec.res f) h1
  have e2 := congrArg (Sec.res f) h2
  rw [res_smul_gen, res_smul_gen] at e1 e2 ⊢
  rw [twGen_pow _ _ _ a ha, smul_smul] at e1 e2 ⊢
  have f1 := ann2 _ l _ _ _ e1
  have f2 := ann2 _ l _ _ _ e2
  rw [mul_smul, f2, smul_smul, mul_comm c, mul_smul, f1, smul_smul]
  congr 1
  subst h
  rw [zpow_add]
  apply ULift.ext
  simp only [ULift.mul_down, Units.val_mul]
  ring

def Good {q : ℕ} {j k l : ℤ} {X : Scheme.{0}} (y : Sec (tw q k) X) (x : Sec (tw q j) X) (z : Sec (tw q l) X) : Prop :=
  (y = 0 ∧ z = 0) ∨ ∃ (ζ : Prim q Γ(X, ⊤)) (c d : ULift.{1} (ZMod q)),
    x = c • twGen j ζ ∧ y = d • twGen k ζ ∧ z = (c * d) • twGen l ζ

theorem Good.res {q : ℕ} {j k l : ℤ} {X Y : Scheme.{0}} {y : Sec (tw q k) X} {x : Sec (tw q j) X} {z : Sec (tw q l) X}
    (hg : Good y x z) (f : Y ⟶ X) : Good (Sec.res f y) (Sec.res f x) (Sec.res f z) := by
  rcases hg with ⟨rfl, rfl⟩ | ⟨ζ, c, d, rfl, rfl, rfl⟩
  · exact Or.inl ⟨map_zero _, map_zero _⟩
  · exact Or.inr ⟨_, c, d, res_smul_gen _ _ _, res_smul_gen _ _ _, res_smul_gen _ _ _⟩

theorem Good.uniq (hR : RootPow) {q : ℕ} {j k l : ℤ} (h : j + k = l) {X : Scheme.{0}} {y : Sec (tw q k) X}
    {x : Sec (tw q j) X} {z z' : Sec (tw q l) X} (hg : Good y x z) (hg' : Good y x z') : z = z' := by
  rcases hg with ⟨hy, hz⟩ | ⟨ζ, c, d, hx, hy, hz⟩ <;> rcases hg' with ⟨hy', hz'⟩ | ⟨ξ, c', d', hx', hy', hz'⟩
  · rw [hz, hz']
  · rw [hz, hz', mul_smul, ann k l ξ d' (hy'.symm.trans hy), smul_zero]
  · rw [hz, hz', mul_smul, ann k l ζ d (hy.symm.trans hy'), smul_zero]
  · rw [hz, hz']
    exact wd hR h _ _ _ _ _ _ (hx.symm.trans hx') (hy.symm.trans hy')

theorem locGen' (hR : RootPow) {q : ℕ} {j : ℤ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X) :
    ∃ S ∈ Scheme.etaleTopology X, ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f →
      ∃ c : ULift.{1} (ZMod q), Sec.res f x = c • twGen j (ζ.map f.appTop.hom) := by
  obtain ⟨S, hS, hp⟩ := LocGen_of hR q j X ζ x
  refine ⟨S, hS, fun Y f hf => ?_⟩
  obtain ⟨c, hc⟩ := hp f hf
  exact ⟨c, hc.trans (Int.cast_smul_eq_zsmul _ _ _).symm⟩

def locSieve {q : ℕ} {j k : ℤ} (l : ℤ) {X : Scheme.{0}} (y : Sec (tw q k) X) (x x' : Sec (tw q j) X) : Sieve X where
  arrows Y f := ∃ z z' : Sec (tw q l) Y, Good (Sec.res f y) (Sec.res f x) z ∧ Good (Sec.res f y) (Sec.res f x') z' ∧
    Good (Sec.res f y) (Sec.res f (x + x')) (z + z')
  downward_closed := by
    rintro Y Z f ⟨z, z', h1, h2, h3⟩ g
    refine ⟨Sec.res g z, Sec.res g z', ?_, ?_, ?_⟩
    · rw [res_comp, res_comp]; exact h1.res g
    · rw [res_comp, res_comp]; exact h2.res g
    · rw [res_comp, res_comp]
      have := h3.res g
      rwa [show Sec.res g (z + z') = Sec.res g z + Sec.res g z' from map_add _ _ _] at this

theorem locSieve_mem (hR : RootPow) {q : ℕ} {j k : ℤ} (l : ℤ) {X : Scheme.{0}} (y : Sec (tw q k) X) (x x' : Sec (tw q j) X) :
    locSieve l y x x' ∈ Scheme.etaleTopology X := by
  obtain ⟨S, hS, hv⟩ := locPres y
  refine Scheme.etaleTopology.transitive hS _ (fun Y f hf => ?_)
  obtain ⟨v, hv⟩ := hv f hf
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  by_cases hne : Nonempty (Prim q Γ(Y, ⊤))
  · obtain ⟨ζ⟩ := hne
    obtain ⟨S1, hS1, h1⟩ := locGen' hR ζ (Sec.res f y)
    obtain ⟨S2, hS2, h2⟩ := locGen' hR ζ (Sec.res f x)
    obtain ⟨S3, hS3, h3⟩ := locGen' hR ζ (Sec.res f x')
    refine Scheme.etaleTopology.superset_covering ?_
      (Scheme.etaleTopology.intersection_covering hS1 (Scheme.etaleTopology.intersection_covering hS2 hS3))
    rintro Z g ⟨g1, g2, g3⟩
    obtain ⟨d, hd⟩ := h1 g g1
    obtain ⟨c, hc⟩ := h2 g g2
    obtain ⟨c', hc'⟩ := h3 g g3
    rw [← res_comp] at hd hc hc'
    refine ⟨_, _, Or.inr ⟨_, c, d, hc, hd, rfl⟩, Or.inr ⟨_, c', d, hc', hd, rfl⟩, Or.inr ⟨_, c + c', d, ?_, hd, ?_⟩⟩
    · rw [add_smul, ← hc, ← hc']
      exact map_add _ _ _
    · rw [add_mul, add_smul]
  · have hw : w = 0 := by
      ext ξ
      exact (hne ⟨ξ⟩).elim
    have hy : Sec.res f y = 0 := by
      rw [hv, hw]
      exact map_zero _
    have hm : locSieve l y x x' f := ⟨0, 0, Or.inl ⟨hy, rfl⟩, Or.inl ⟨hy, rfl⟩, Or.inl ⟨hy, add_zero _⟩⟩
    rw [Sieve.pullback_eq_top_of_mem _ hm]
    exact Scheme.etaleTopology.top_mem _

def Rel {q : ℕ} {j k l : ℤ} {X : Scheme.{0}} (y : Sec (tw q k) X) (x : Sec (tw q j) X) (z : Sec (tw q l) X) : Prop :=
  ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X) (t : Sec (tw q l) Y), Good (Sec.res f y) (Sec.res f x) t → Sec.res f z = t

theorem rel_ex (hR : RootPow) {q : ℕ} {j k l : ℤ} (h : j + k = l) {X : Scheme.{0}} (y : Sec (tw q k) X) (x : Sec (tw q j) X) :
    ∃ z : Sec (tw q l) X, Rel y x z := by
  have hS := locSieve_mem hR l y x x
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget _)).obj (tw q l)).2 _ hS
  have hz : ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), locSieve l y x x f → ∃ z : Sec (tw q l) Y, Good (Sec.res f y) (Sec.res f x) z :=
    fun Y f hf => hf.imp fun _ hz => hz.choose_spec.1
  choose z hz using hz
  obtain ⟨t, ht, -⟩ := hsh z (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e => by
    have a1 := (hz f₁ h₁).res g₁
    have a2 := (hz f₂ h₂).res g₂
    rw [← res_comp, ← res_comp] at a1 a2
    rw [e] at a1
    exact a1.uniq hR h a2)
  refine ⟨t, fun Y f s hs => ?_⟩
  refine sep _ (Scheme.etaleTopology.pullback_stable f hS) _ _ (fun Z g hg => ?_)
  have e : Sec.res (F := tw q l) (g ≫ f) t = z (g ≫ f) hg := ht (g ≫ f) hg
  refine (res_comp g f t).symm.trans (e.trans ?_)
  have a1 := hs.res g
  rw [← res_comp, ← res_comp] at a1
  exact (hz _ hg).uniq hR h a1

theorem Rel.res {q : ℕ} {j k l : ℤ} {X Y : Scheme.{0}} {y : Sec (tw q k) X} {x : Sec (tw q j) X} {z : Sec (tw q l) X}
    (hr : Rel y x z) (f : Y ⟶ X) : Rel (Sec.res f y) (Sec.res f x) (Sec.res f z) := by
  intro Z g t ht
  rw [← res_comp, ← res_comp] at ht
  rw [← res_comp]
  exact hr _ t ht

theorem Rel.uniq (hR : RootPow) {q : ℕ} {j k l : ℤ} {X : Scheme.{0}} {y : Sec (tw q k) X}
    {x : Sec (tw q j) X} {z z' : Sec (tw q l) X} (hg : Rel y x z) (hg' : Rel y x z') : z = z' := by
  refine sep _ (locSieve_mem hR l y x x) _ _ ?_
  rintro Y f ⟨t, -, ht, -⟩
  rw [hg f t ht, hg' f t ht]

theorem Gen_of (hR : RootPow) : LateralTheory.E.MulPf.Gen := by
  intro q
  choose m hm using fun (j k l : ℤ) (h : j + k = l) (X : Scheme.{0}) (y : Sec (tw q k) X) (x : Sec (tw q j) X) => rel_ex hR h y x
  refine ⟨fun j k l h X y => AddMonoidHom.mk' (m j k l h X y) (fun x x' => ?_), ?_, ?_⟩
  · refine sep _ (locSieve_mem hR l y x x') _ _ ?_
    rintro Y f ⟨t, t', h1, h2, h3⟩
    rw [hm j k l h X y _ f _ h3, ← hm j k l h X y _ f _ h1, ← hm j k l h X y _ f _ h2]
    exact (map_add _ _ _).symm
  · intro j k l h X Y f y x
    exact ((hm j k l h X y x).res f).uniq hR (hm j k l h Y _ _)
  · intro j k l h X ζ
    refine sep ⊤ (Scheme.etaleTopology.top_mem _) _ _ (fun Y f _ => ?_)
    refine hm j k l h X _ _ f _ (Good.res (Or.inr ⟨ζ, 1, 1, ?_, ?_, ?_⟩) f) <;> simp only [mul_one, one_smul]

theorem Gen_of' (hR : LateralTheory.E.MulPf.RootPow) : LateralTheory.E.MulPf.Gen := Gen_of hR

end LateralTheory.E.GenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RootPowPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.RootPowPf

theorem prim_eval {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : IsRoot (cyclotomic q A) ζ.1 := by
  have h := ζ.2.2
  rw [IsRoot.def, ← map_cyclotomic_int q A, Polynomial.eval_map]
  rw [aeval_def] at h
  exact h

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := (prim_eval ζ).dvd (cyclotomic.dvd_X_pow_sub_one q A)
  simpa [IsRoot.def, sub_eq_zero] using h

theorem field_case {q : ℕ} {K : Type} [Field K] (ζ ξ : Prim q K) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  have : NeZero q := NeZero.of_neZero_natCast K
  have hζ : IsPrimitiveRoot ζ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ζ)
  have hξ : IsPrimitiveRoot ξ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ξ)
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]

theorem local_case {q : ℕ} {O : Type} [CommRing O] [IsLocalRing O] (ζ ξ : Prim q O) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨a, ha⟩ := field_case (ζ.map (IsLocalRing.residue O)) (ξ.map (IsLocalRing.residue O))
  refine ⟨a, ?_⟩
  change IsLocalRing.residue O ξ.1 = (IsLocalRing.residue O ζ.1) ^ _ at ha
  rw [← map_pow] at ha
  set η := ζ.1 ^ (a : ZMod q).val with hη
  have hηq : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, prim_pow, one_pow]
  have hq : q ≠ 0 := by
    rintro rfl
    have := ζ.2.1
    simp at this
  have hηu : IsUnit η := IsUnit.of_pow_eq_one hηq hq
  have hg := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [prim_pow, hηq, sub_self] at hg
  have hu : IsUnit (∑ i ∈ Finset.range q, ξ.1 ^ i * η ^ (q - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp only [map_sum, map_mul, map_pow, ha]
    rw [geom_sum₂_self]
    have h1 : IsUnit ((q : O) * η ^ (q - 1)) := ζ.2.1.mul (hηu.pow _)
    have h2 := (h1.map (IsLocalRing.residue O)).ne_zero
    simpa using h2
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 hg)

def sv {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : Sieve Y where
  arrows := fun Z g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val
  downward_closed := by
    rintro Z W g ⟨a, ha⟩ h
    refine ⟨a, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _ at ha
    change (h ≫ g).appTop.hom ξ.1 = (h ≫ g).appTop.hom ζ.1 ^ _
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ha, map_pow]

theorem nhd {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ sv ζ ξ U.ι := by
  obtain ⟨a, ha⟩ := local_case (ζ.map (Y.presheaf.germ ⊤ y trivial).hom) (ξ.map (Y.presheaf.germ ⊤ y trivial).hom)
  change (Y.presheaf.germ ⊤ y trivial).hom ξ.1 = (Y.presheaf.germ ⊤ y trivial).hom ζ.1 ^ _ at ha
  rw [← map_pow] at ha
  obtain ⟨(U : Y.Opens), hU, i, i', he⟩ := TopCat.Presheaf.germ_eq Y.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ ha
  refine ⟨U, hU, a, ?_⟩
  change U.ι.appTop.hom ξ.1 = U.ι.appTop.hom ζ.1 ^ _
  rw [← map_pow]
  have hf : U.ι.appTop = Y.presheaf.map i.op ≫ U.topIso.inv := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact (Y.presheaf.map_comp _ _).symm ▸ rfl
  have hi : i' = i := Subsingleton.elim _ _
  subst hi
  rw [hf]
  exact congrArg U.topIso.inv.hom he

theorem sv_mem {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : sv ζ ξ ∈ Scheme.etaleTopology Y := by
  apply Scheme.zariskiTopology_le_etaleTopology
  choose U hU hS using nhd ζ ξ
  refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers Y (fun y => (U y : Scheme)) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hU y⟩, rfl⟩) (fun y => inferInstance), ?_⟩
  rintro _ _ ⟨y⟩
  exact hS y

theorem RootPow_of : LateralTheory.E.MulPf.RootPow := by
  classical
  intro q Y ζ s
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ ξ h => absurd h (Finset.notMem_empty ξ)⟩
  | insert ξ s _ ih =>
    obtain ⟨S, hS, h⟩ := ih
    refine ⟨S ⊓ sv ζ ξ, GrothendieckTopology.intersection_covering _ hS (sv_mem ζ ξ), ?_⟩
    rintro Z g ⟨h1, h2⟩ η hη
    rcases Finset.mem_insert.1 hη with rfl | hη
    · exact h2
    · exact h g h1 η hη

end LateralTheory.E.RootPowPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SysFMPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.SysFMPf

def phi {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Γ(w.normalization, ⊤) →+* W :=
  (w.toNormalization.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom

def RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) : Set w.normalization :=
  {y | ∀ s : Γ(w.normalization, ⊤), IsIdempotentElem (phi w s) → phi w s ∉ q.asIdeal → y ∈ w.normalization.basicOpen s}

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ⋂ j, Set.range (ι j) = RR w q

def FMex : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m ∧
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization ∧
      Mono m ∧ Flat m ∧ QuasiCompact m

def FMrange : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ (q : PrimeSpectrum W)
    (m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization),
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m →
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization →
      Set.range m = RR w q

theorem SysFM_of (hS : Sys) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hS W w hW y
  obtain ⟨m, e1, e2, hm, hf, hq⟩ := hE W w hW q
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, m, hm, hf, hq, ?_⟩
  rw [h3]
  exact hR W w hW q m e1 e2

end LateralTheory.E.SysFMPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncBijPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {K K' L : CochainComplex C ℤ}

def preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) : Cochain K L j := (Cochain.ofHom g).comp z (zero_add j)

theorem preC_v (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (p q : ℤ) (h : p + j = q) :
    (preC g z).v p q h = g.f p ≫ z.v p q h := by
  simp [preC]

theorem δ_preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (k : ℤ) : δ j k (preC g z) = preC g (δ j k z) :=
  δ_ofHom_comp g z k

theorem preC_zero (g : K ⟶ K') (j : ℤ) : preC g (0 : Cochain K' L j) = 0 := by
  simp [preC]

theorem preC_inj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) {x y : Cochain K' L j}
    (h : preC g x = preC g y) : x = y := by
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have := hg p (by omega)
    have h' := congrArg (fun z : Cochain K L j => z.v p q hpq) h
    simp only [preC_v] at h'
    exact (cancel_epi (g.f p)).1 h'

theorem preC_surj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) (y : Cochain K L j) :
    ∃ x : Cochain K' L j, preC g x = y := by
  refine ⟨Cochain.mk fun p q hpq =>
    if h : -(n + 1) ≤ p then (haveI := hg p h; inv (g.f p)) ≫ y.v p q hpq else 0, ?_⟩
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have hp : -(n + 1) ≤ p := by omega
    rw [preC_v, Cochain.mk_v, dif_pos hp, IsIso.hom_inv_id_assoc]

end General

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) :=
  CochainComplex.isZero_of_isStrictlyGE (injectiveResolution F).cochainComplex 0 q hq

theorem pull_mk (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (m : ℤ) (x : Cocycle K' (res R F) m) :
    ∃ y : Cocycle K (res R F) m, HK.pull R g F m (CohomologyClass.mk x) = CohomologyClass.mk y ∧
      (y : Cochain K (res R F) m) = preC g (x : Cochain K' (res R F) m) :=
  ⟨_, rfl, rfl⟩

end LateralTheory.E.TruncBijPf

open LateralTheory.E.TruncBijPf in
theorem LateralTheory.E.TruncPf.TruncBij_of : LateralTheory.E.TruncPf.TruncBij := by
  intro R _ F K K' g n hg m hm
  have hL := res_isZero R F
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, hy, hy'⟩ := pull_mk R F g m x
    rw [hy, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := preC_surj g n hg hL (by omega) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)]
    refine ⟨β', preC_inj g n hg hL (by omega) ?_⟩
    rw [← δ_preC, hβ, hy']
  · intro y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨x, hx⟩ := preC_surj g n hg hL (j := m) (by omega) (y : Cochain K (res R F) m)
    have hδ : δ m (m + 1) x = 0 := by
      apply preC_inj g n hg hL (by omega)
      rw [← δ_preC, hx, preC_zero, Cocycle.δ_eq_zero]
    obtain ⟨y', hy, hy'⟩ := pull_mk R F g m (Cocycle.mk x (m + 1) rfl hδ)
    refine ⟨_, hy.trans (congrArg CohomologyClass.mk (Cocycle.ext ?_))⟩
    rw [hy', ← hx]
    rfl
end
end

