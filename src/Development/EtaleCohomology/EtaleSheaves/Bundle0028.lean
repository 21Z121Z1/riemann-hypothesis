import Development.EtaleCohomology.EtaleSheaves.Bundle0013
import Development.EtaleCohomology.TateTwists.Bundle0010
import Development.EtaleCohomology.EtaleSheaves.Bundle0014
import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.Bundle0015

-- bundled from Development.EtaleCohomology.EtaleSheaves.MVSpcPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.MVSpcPf

def Ses : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w,
  (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact

variable {R : Type} [CommRing R] {I : Cx R}

abbrev pc {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : Cochain K I m := (Cochain.ofHom φ).comp z (zero_add m)

theorem pc_comp {K L M : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {m : ℤ} (z : Cochain M I m) : pc (φ ≫ ψ) z = pc φ (pc ψ z) := by
  simp [pc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem pc_addm {K L : Cx R} (φ ψ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (φ + ψ) z = pc φ z + pc ψ z := by
  simp [pc, Cochain.ofHom_add, Cochain.add_comp]

theorem pc_negm {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (-φ) z = -pc φ z := by
  simp [pc, Cochain.ofHom_neg, Cochain.neg_comp]

theorem pc_zerom {K L : Cx R} {m : ℤ} (z : Cochain L I m) : pc (0 : K ⟶ L) z = 0 := by
  simp [pc, Cochain.ofHom_zero, Cochain.zero_comp]

theorem pc_add {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z + z') = pc φ z + pc φ z' := by
  simp [pc, Cochain.comp_add]

theorem pc_sub {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z - z') = pc φ z - pc φ z' := by
  simp [pc, Cochain.comp_sub]

theorem pc_δ {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) (m' : ℤ) : δ m m' (pc φ z) = pc φ (δ m m' z) :=
  δ_ofHom_comp φ z m'

theorem cpre_mk' {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cocycle L I m) :
    cpre (Cocycle.ofHom φ) I m m (zero_add m) (CohomologyClass.mk z) =
      CohomologyClass.mk (Cocycle.mk (pc φ z.1) (m + 1) rfl (by rw [pc_δ, Cocycle.δ_eq_zero, pc, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

theorem cocy_δ {K : Cx R} {m : ℤ} (z : Cocycle K I m) (m' : ℤ) : δ m m' z.1 = 0 := by
  by_cases h : m + 1 = m'
  · exact (Cocycle.mem_iff m m' h z.1).1 z.2
  · exact δ_shape _ _ h _

theorem chase (hI : ∀ n, Injective (I.X n)) {K1 KA KB K3 : Cx R} (φ : K1 ⟶ KA) (ψ : K1 ⟶ KB) (u : KA ⟶ K3)
    (v : KB ⟶ K3) (w) (hS : (ShortComplex.mk (biprod.lift φ (-ψ)) (biprod.desc u v) w).ShortExact) (n : ℤ)
    (hc : ∀ c : CohomologyClass K1 I n, ∃ a b, c = cpre (Cocycle.ofHom φ) I n n (zero_add n) a -
      cpre (Cocycle.ofHom ψ) I n n (zero_add n) b)
    (x : CohomologyClass K3 I (n + 1)) (hu : cpre (Cocycle.ofHom u) I _ _ (zero_add _) x = 0)
    (hv : cpre (Cocycle.ofHom v) I _ _ (zero_add _) x = 0) : x = 0 := by
  have hC := fun m => LateralTheory.EtaleFoundations.etale_simplicial_cochain_short_exact_sequence_holds R I hI _ hS m
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [cpre_mk', CohomologyClass.mk_eq_zero_iff] at hu hv
  obtain ⟨m, hm, aU, haU⟩ := hu
  obtain ⟨m', hm', aV, haV⟩ := hv
  have e1 : n = m := by omega
  subst e1
  have e2 : n = m' := by omega
  subst e2
  simp only [Cocycle.mk_coe] at haU haV
  set b : Cochain (KA ⊞ KB) I n := pc biprod.fst aU + pc biprod.snd aV with hbdef
  have hb : δ n (n + 1) b = pc (biprod.desc u v) z.1 := by
    rw [hbdef, δ_add, pc_δ, pc_δ, haU, haV, ← pc_comp, ← pc_comp, ← pc_addm, ← biprod.desc_eq]
  have hαb : δ n (n + 1) (pc (biprod.lift φ (-ψ)) b) = 0 := by
    rw [pc_δ, hb, ← pc_comp, w, pc_zerom]
  obtain ⟨a, b0, hab⟩ := hc (CohomologyClass.mk (Cocycle.mk (pc (biprod.lift φ (-ψ)) b) (n + 1) rfl hαb))
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b0, rfl⟩ := b0.mk_surjective
  rw [cpre_mk', cpre_mk', ← CohomologyClass.mk_sub, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff] at hab
  obtain ⟨k, hk, e, he⟩ := hab
  obtain ⟨e2, he2⟩ := (hC k).1 e
  set b2 : Cochain (KA ⊞ KB) I n := pc biprod.fst a.1 + pc biprod.snd b0.1 with hb2def
  have hαb2 : pc (biprod.lift φ (-ψ)) b2 = pc φ a.1 - pc ψ b0.1 := by
    rw [hb2def, pc_add, ← pc_comp, ← pc_comp, biprod.lift_fst, biprod.lift_snd, pc_negm, sub_eq_add_neg]
  have hδb2 : δ n (n + 1) b2 = 0 := by
    rw [hb2def, δ_add, pc_δ, pc_δ, cocy_δ, cocy_δ, pc, pc, Cochain.comp_zero, Cochain.comp_zero, add_zero]
  have hr : pc (biprod.lift φ (-ψ)) (b - b2 - δ k n e2) = 0 := by
    have he2' : pc (biprod.lift φ (-ψ)) e2 = e := he2
    rw [pc_sub, pc_sub, ← pc_δ, he2', he]
    change _ - _ - (pc (biprod.lift φ (-ψ)) b - (pc φ a.1 - pc ψ b0.1)) = 0
    rw [hαb2]; abel
  obtain ⟨c3, hc3⟩ := (hC n).2.1 _ hr
  have hc3' : pc (biprod.desc u v) c3 = _ := hc3
  have hz : pc (biprod.desc u v) (δ n (n + 1) c3 - z.1) = 0 := by
    rw [pc_sub, ← pc_δ]
    change δ n (n + 1) (pc (biprod.desc u v) c3) - _ = 0
    rw [hc3', δ_sub, δ_sub, δ_δ, hδb2, hb]; simp
  have := (hC (n + 1)).2.2 _ hz
  exact (CohomologyClass.mk_eq_zero_iff _).2 ⟨n, rfl, c3, sub_eq_zero.1 this⟩

end LateralTheory.E.MVSpcPf

open LateralTheory.E.MVSpcPf in
theorem LateralTheory.E.MVPf.MVSpc_of (hS : Ses) : LateralTheory.E.MVPf.MVSpc := by
  intro _ R _ F U V E f g hc n hd x hxf hxg
  obtain ⟨w, hw⟩ := hS R f g hc
  have hI : ∀ k, Injective ((res R F).X k) := fun k => by unfold res; infer_instance
  exact chase hI _ _ _ _ w hw n hd x hxf hxg
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.OpenCovPtaPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.OpenCov_ptaPf

variable (R : Type) [CommRing R]

abbrev gen (P : PSh) {W : Scheme.{0}ᵒᵖ} (x : P.obj W) : ((freeP R).obj P).obj W :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj W)) (ULift.up x)

abbrev adj {P : PSh} {G : Shv R} (a : (free R).obj P ⟶ G) : (freeP R).obj P ⟶ G.obj :=
  toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ a.hom

theorem adj_inj {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G) (h : adj R a = adj R b) : a = b := by
  ext1
  exact sheafify_hom_ext _ _ _ G.property h

theorem adj_comp {P Q : PSh} {G : Shv R} (φ : P ⟶ Q) (a : (free R).obj Q ⟶ G) :
    adj R ((free R).map φ ≫ a) = (freeP R).map φ ≫ adj R a := by
  show toSheafify _ _ ≫ (sheafifyMap _ ((freeP R).map φ) ≫ a.hom) = _
  show _ = (freeP R).map φ ≫ toSheafify _ _ ≫ a.hom
  erw [toSheafify_naturality_assoc]

theorem freePresheaf_obj_map_freeMk (P : PSh) {W W' : Scheme.{0}ᵒᵖ} (h : W ⟶ W') (x : P.obj W) :
    ((freeP R).obj P).map h (gen R P x) = gen R P (P.map h x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem freePresheaf_map_freeMk {P Q : PSh} (φ : P ⟶ Q) (W : Scheme.{0}ᵒᵖ) (x : P.obj W) :
    ((freeP R).map φ).app W (gen R P x) = gen R Q (φ.app W x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem adj_val {X Y : Scheme.{0}} {G : Shv R} (a : (free R).obj (yoneda.obj X) ⟶ G) (x : Y ⟶ X) :
    (adj R a).app (op Y) (gen R (yoneda.obj X) (W := op Y) x) =
      G.obj.map x.op ((adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X))) := by
  rw [← ConcreteCategory.comp_apply, ← (adj R a).naturality, ConcreteCategory.comp_apply, freePresheaf_obj_map_freeMk]
  simp

theorem ext_of_cover {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hcov : Set.range f ∪ Set.range g = Set.univ) {G : Shv R} (a b : (free R).obj (yoneda.obj X) ⟶ G)
    (hf : (free R).map (yoneda.map f) ≫ a = (free R).map (yoneda.map f) ≫ b)
    (hg : (free R).map (yoneda.map g) ≫ a = (free R).map (yoneda.map g) ≫ b) : a = b := by
  let Z : Bool → Scheme.{0} := fun i => Bool.rec V U i
  let φ : ∀ i, Z i ⟶ X := fun i => Bool.rec (motive := fun i => Z i ⟶ X) g f i
  have hS : Sieve.ofArrows Z φ ∈ Scheme.etaleTopology X := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : x ∈ Set.range f ∪ Set.range g := hcov ▸ Set.mem_univ x
      rcases hx with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · cases i <;> infer_instance
  have hf' := congrArg (adj R) hf
  have hg' := congrArg (adj R) hg
  rw [adj_comp, adj_comp] at hf' hg'
  have key : (adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) =
      (adj R b).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) := by
    refine Presheaf.IsSheaf.isSeparated G.property _ _ hS _ _ ?_
    intro Y' h hh
    obtain ⟨W, k, _, ⟨i⟩, rfl⟩ := hh
    rw [← adj_val, ← adj_val]
    cases i
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj V) (W := op _) k)) hg'
      simpa [freePresheaf_map_freeMk] using this
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj U) (W := op _) k)) hf'
      simpa [freePresheaf_map_freeMk] using this
  apply adj_inj
  ext Y : 2
  induction Y with | op Y => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact (adj_val R a x).trans ((congrArg _ key).trans (adj_val R b x).symm)

theorem openCov : LateralTheory.E.MayerVietorisSequence.OpenCov := by
  intro R _ U V X f g _ _ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  have : sch.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  refine ⟨inferInstance, inferInstance, fun n => ⟨fun {G} a b h => ?_⟩⟩
  apply ext_of_cover R f g hcov a b
  · have h1 : (free R).map ((sch.map f).app n) ≫ a = (free R).map ((sch.map f).app n) ≫ b := by
      simpa using congrArg (biprod.inl ≫ ·) h
    exact h1
  · have h1 : (free R).map ((sch.map g).app n) ≫ a = (free R).map ((sch.map g).app n) ≫ b := by
      simpa using congrArg (biprod.inr ≫ ·) h
    exact h1

end LateralTheory.E.OpenCov_ptaPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PiecesPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.PiecesPf

lemma sq1 {T S C' C : Type} [CommRing T] [CommRing S] [CommRing C'] [CommRing C]
    (a : T →+* C') (π : T →+* S) (ρ : C' →+* C) (b : S →+* C) (hρ : Function.Surjective ρ) (hπ : Function.Surjective π)
    (hcomm : ρ.comp a = b.comp π) (hker : RingHom.ker ρ = (RingHom.ker π).map a) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom π) (CommRingCat.ofHom ρ) (CommRingCat.ofHom b) := by
  have w : CommRingCat.ofHom a ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom π ≫ CommRingCat.ofHom b := by
    ext x; exact congrArg (fun f : T →+* C => f x) hcomm
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w ?_ ?_ ?_ ?_)
  · intro s
    refine CommRingCat.ofHom (ρ.liftOfSurjective hρ ⟨s.inl.hom, ?_⟩)
    rw [hker, Ideal.map_le_iff_le_comap]
    intro t ht
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    simp only [Ideal.mem_comap, RingHom.mem_ker] at ht ⊢
    rw [h1, ht, map_zero]
  · intro s
    ext x
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    exact RingHom.liftOfSurjective_comp_apply ρ hρ _ x
  · intro s
    ext x
    obtain ⟨t, rfl⟩ := hπ x
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 ⊢
    rw [← RingHom.comp_apply b π, ← hcomm, RingHom.comp_apply, RingHom.liftOfSurjective_comp_apply]
    exact h1
  · intro s m hm _
    ext x
    obtain ⟨y, rfl⟩ := hρ x
    simp only [CommRingCat.hom_ofHom]
    rw [RingHom.liftOfSurjective_comp_apply]
    have := congrArg (fun f => f.hom y) hm
    simpa using this

theorem Pieces_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) :
    LateralTheory.E.FinEtSectionPf.Pieces := by
  intro _ _ S C _ _ _ _ hQA
  obtain ⟨T, _, _, π, hAIC, hπ⟩ := hQA
  obtain ⟨C', _, _, ρ, hEt, hρ, hcomm, hker⟩ := hL T S C π hπ
  have := hEt
  obtain ⟨n, e', he', hoi⟩ := hA T C' hAIC
  refine ⟨n, ρ ∘ e', he'.map ρ, fun j => ?_⟩
  let fₘ : Localization.Away (e' j) →+* Localization.Away (ρ (e' j)) :=
    IsLocalization.Away.map _ _ ρ (e' j)
  have : IsLocalization ((Submonoid.powers (e' j)).map ρ) (Localization.Away (ρ (e' j))) := by
    rw [Submonoid.map_powers]; infer_instance
  have H : fₘ.comp (algebraMap C' _) = (algebraMap C _).comp ρ := IsLocalization.map_comp _
  have sq2 := CommRingCat.isPushout_of_isLocalization ρ fₘ H (Submonoid.powers (e' j))
  have sq := (sq1 (algebraMap T C') π ρ (algebraMap S C) hρ hπ hcomm hker).paste_horiz sq2.flip
  have pb := isPullback_SpecMap_of_isPushout _ _ _ _ sq
  have hj := hoi j
  rw [CommRingCat.ofHom_comp] at hj
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) pb hj
  rw [CommRingCat.ofHom_comp]
  exact this

end LateralTheory.E.PiecesPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PrimMapComp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.Deg0Pf

theorem exists_prim (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hA : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  obtain ⟨z, hz⟩ : ∃ z : S, (Polynomial.cyclotomic q S).eval z = 0 := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exact ⟨0, Subsingleton.elim _ _⟩
    · exact hA _ (Polynomial.cyclotomic.monic q S) (by
        rw [Polynomial.natDegree_cyclotomic]
        exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (ζ : Prim q A) : (ζ.map f).map g = ζ.map (g.comp f) := rfl

theorem rL_comp {S : Type} [CommRing S] (f g : S) :
    (rL f g).comp (algebraMap S (Localization.Away f)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_comp {S : Type} [CommRing S] (f g : S) :
    (rR f g).comp (algebraMap S (Localization.Away g)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem Deg0_of : LateralTheory.E.AcycQAPf.Deg0 := by
  intro hQ hH hL h9 q _ i S _ hS hq f g hfg c
  obtain ⟨e, he⟩ := hH h9 q i
  obtain ⟨ζ⟩ := exists_prim q S (hQ S hS).1 hq
  obtain ⟨a, b, hab⟩ := hL q S hS f g hfg ((e _ (ζ.map (algebraMap S (Localization.Away (f * g))))).symm c)
  refine ⟨e _ (ζ.map (algebraMap S (Localization.Away f))) a, e _ (ζ.map (algebraMap S (Localization.Away g))) b, ?_⟩
  rw [he, he, prim_map_comp, prim_map_comp, rL_comp, rR_comp, ← map_sub, ← hab, AddEquiv.apply_symm_apply]

end LateralTheory.E.Deg0Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProEqvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.ProEqvPf

def fm {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (u : U ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of A)) :
    pullback (u ≫ g) (cpt A) ⟶ pullback g (cpt A) :=
  pullback.map _ _ _ _ u (𝟙 _) (𝟙 _) (by simp) (by simp)

def Hit (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) : Prop :=
  ∃ w : Ht q (sch.obj U) n i, pull _ (sch.map (pullback.fst (u ≫ g) (cpt A))) _ _ w = pull _ (sch.map (fm u g)) _ _ z

def PiLocalization₂ : Prop := Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∃ j, pull _ (sch.map (ι j)) _ _ x = 0) ∧
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

def Glue : Prop := MV → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (n : ℤ),
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ pull _ (sch.map u) _ _ x = 0) →
  (∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ Hit q i n g z u) →
  Function.Bijective (pull _ (sch.map (pullback.fst g (cpt A))) (tw q i) n)

theorem ProEqv_of (hC : Cont) (hM : MV) (hS : PiLocalization₂) (hG : Glue) : ProEqv := by
  intro H q i A _ _ hq Y _ _ g hY n
  refine hG hM H q i A hq g n (fun x hx y => ?_) (fun z y => ?_)
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).1 x hx
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).2 z
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩

end LateralTheory.E.ProEqvPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProdAcycPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ProdAcycPf

theorem zero_acyc (H : LateralTheory.E.t_E2Cut.Hyp) (q : ℕ) (A : Type) [CommRing A] [Subsingleton A] : Acyc q (sp A) := by
  intro n i hn
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : Ht q (sp A) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, -, -, hx⟩ := H.a5 (ZMod q) (Spec (CommRingCat.of A)) (tw q i) n hn x
    have : IsEmpty (Spec (CommRingCat.of A)) := inferInstanceAs (IsEmpty (PrimeSpectrum A))
    have : IsIso (sch.map f) := inferInstance
    have hy : pull _ (inv (sch.map f)) _ _ (pull _ (sch.map f) _ _ x) = x := by
      rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    rw [← hy, hx, map_zero]
  rw [h0 x, h0 y]

def Bin : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1],
  Nonempty (A ≃+* R0 × R1) → Acyc q (sp R0) → Acyc q (sp R1) → Acyc q (sp A)

def splitFirst (n : ℕ) (R : Fin (n + 1) → Type) [∀ k, CommRing (R k)] :
    (∀ k, R k) ≃+* R 0 × ∀ k : Fin n, R k.succ where
  toFun f := (f 0, fun k => f k.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem prod_of (hB : Bin) : LateralTheory.E.QuotAcycCut.ProdAcyc := by
  intro H q A _ n
  induction n generalizing A with
  | zero =>
    intro R _ ⟨e⟩ _
    have : Subsingleton A := e.injective.subsingleton
    exact zero_acyc H q A
  | succ n ih =>
    intro R _ ⟨e⟩ hR
    refine hB H q A (R 0) (∀ k : Fin n, R k.succ) ⟨e.trans (splitFirst n R)⟩ (hR 0) ?_
    exact ih (∀ k : Fin n, R k.succ) (fun k => R k.succ) ⟨RingEquiv.refl _⟩ fun k => hR k.succ

end LateralTheory.E.ProdAcycPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelNormPfGlue
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

def ClosedAt {X T : Scheme.{0}} (c : X ⟶ T) (W : T.Opens) : Prop :=
  ∀ b : Γ(X, c ⁻¹ᵁ W), (c.app W).hom.IsIntegralElem b → ∃ a, c.app W a = b

theorem app_res_apply {X T : Scheme.{0}} (c : X ⟶ T) {W V : T.Opens} (h : W ⟶ V) (a : Γ(T, V)) :
    c.app W (T.presheaf.map h.op a) =
      X.presheaf.map (homOfLE (c.preimage_mono h.le)).op (c.app V a) := by
  rw [← CommRingCat.comp_apply, c.naturality, CommRingCat.comp_apply]; rfl

theorem integral_res {X T : Scheme.{0}} (c : X ⟶ T) {W V : T.Opens} (h : W ≤ V) (b : Γ(X, c ⁻¹ᵁ V))
    (hb : (c.app V).hom.IsIntegralElem b) :
    (c.app W).hom.IsIntegralElem (X.presheaf.map (homOfLE (c.preimage_mono h)).op b) := by
  obtain ⟨p, hm, hp⟩ := hb
  refine ⟨p.map (T.presheaf.map (homOfLE h).op).hom, hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have e : (c.app W).hom.comp (T.presheaf.map (homOfLE h).op).hom =
      (X.presheaf.map (homOfLE (c.preimage_mono h)).op).hom.comp (c.app V).hom := by
    ext a; exact app_res_apply c (homOfLE h) a
  rw [e, ← Polynomial.hom_eval₂, hp, map_zero]

theorem closedAt_of_local {X T : Scheme.{0}} (c : X ⟶ T) (hinj : ∀ W, Function.Injective (c.app W))
    (V : T.Opens) (hloc : ∀ x ∈ V, ∃ W, W ≤ V ∧ x ∈ W ∧ ClosedAt c W) : ClosedAt c V := by
  intro b hb
  choose W hWV hxW hW using fun x : V => hloc x.1 x.2
  choose a ha using fun x : V => hW x _ (integral_res c (hWV x) b hb)
  have hcomp : TopCat.Presheaf.IsCompatible T.sheaf.obj W a := by
    intro i j
    apply hinj
    have h1 := app_res_apply c (TopologicalSpace.Opens.infLELeft (W i) (W j)) (a i)
    have h2 := app_res_apply c (TopologicalSpace.Opens.infLERight (W i) (W j)) (a j)
    erw [h1, h2, ha, ha]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  obtain ⟨s, hs, -⟩ := T.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩) a hcomp
  refine ⟨s, X.sheaf.eq_of_locally_eq' (fun i => c ⁻¹ᵁ W i) (c ⁻¹ᵁ V)
    (fun i => homOfLE (c.preimage_mono (hWV i))) ?_ _ _ fun i => ?_⟩
  · intro z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨c z, hz⟩, hxW ⟨c z, hz⟩⟩
  · have h1 := app_res_apply c (homOfLE (hWV i)) s
    erw [hs i, ha i] at h1
    exact h1.symm

def NormClosed : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], IsIntegral Z →
  ∀ V : g.normalization.Opens, IsAffineOpen V → ∀ b : Γ(Z, g.toNormalization ⁻¹ᵁ V),
    (g.toNormalization.app V).hom.IsIntegralElem b → ∃ a, g.toNormalization.app V a = b

def NormLocal : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], IsIntegral Z →
  ∀ U : S.Opens, IsAffineOpen U → ∀ t : Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U),
    ClosedAt g.toNormalization (g.normalization.basicOpen t)

theorem NormClosed_of (hL : NormLocal) : NormClosed := by
  intro Z S g _ _ hZ V hV
  have : IsSchemeTheoreticallyDominant g.toNormalization := .of_isDominant _
  refine closedAt_of_local _ (fun W => g.toNormalization.app_injective W) V fun x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.fromNormalization x)) isOpen_univ
  have hU' : IsAffineOpen (g.fromNormalization ⁻¹ᵁ U) := hU.preimage _
  obtain ⟨f, f', e, hxf⟩ := exists_basicOpen_le_affine_inter hU' hV x ⟨hxU, hx⟩
  exact ⟨_, e ▸ g.normalization.basicOpen_le f', hxf, hL g hZ U hU f⟩

theorem RelNorm_of_closed (hN : NormClosed) : LateralTheory.E.SteinPf.RelNorm := by
  intro Z S g _ _ hZ
  haveI : IsIntegral Z := hZ.1
  refine ⟨g.normalization, g.toNormalization, g.fromNormalization, inferInstance, inferInstance, inferInstance,
    g.toNormalization_fromNormalization, fun V hV hne => ⟨?_, ?_, hN g hZ.1 V hV⟩⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨z, hz⟩ := g.toNormalization.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
    exact ⟨z, hz⟩
  · haveI : IsSchemeTheoreticallyDominant g.toNormalization := .of_isDominant _
    exact g.toNormalization.app_injective V

end LateralTheory.E.RelNormPf
end
end

