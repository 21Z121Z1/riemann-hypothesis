import Development.EtaleCohomology.TateTwists.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0003
import Development.EtaleCohomology.TateTwists.Bundle0005
import Development.EtaleCohomology.TateTwists.Bundle0002

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvDeltaPf

variable {R : Type} [CommRing R]

def secHom {F G : Shv R} (U : Scheme.{0}) (x : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := Sec.map φ x
  map_zero' := by simp [Sec.map]
  map_add' f g := by simp [Sec.map]

lemma sec_zsmul {F G : Shv R} (f : F ⟶ G) (c : ℤ) (U : Scheme.{0}) (x : Sec F U) : Sec.map (c • f) x = c • Sec.map f x :=
  map_zsmul (secHom (G := G) U x) c f

lemma sec_sum {ι : Type} (s : Finset ι) {F G : Shv R} (f : ι → (F ⟶ G)) (U : Scheme.{0}) (x : Sec F U) : Sec.map (∑ i ∈ s, f i) x = ∑ i ∈ s, Sec.map (f i) x :=
  map_sum (secHom (G := G) U x) f s

variable (R) in
lemma freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) : Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  calc _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := rfl
    _ = (((freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := by rw [toSheafify_naturality]
    _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) := rfl
    _ = _ := by
      unfold freeGen
      congr 1
      simp [freeP, ModuleCat.freeMk]
      exact Finsupp.mapDomain_single

variable (R) in
lemma chains_d (E : Spc) (p : ℕ) : (chainsXIso R E (p+1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (chainsXIso R E (p+1)).hom ≫ ((chainsN R).obj E).d (p+1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq _ _ rfl rfl
  have h2 : ((chainsN R).obj E).d (p+1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
    simp [chainsN]
    rfl
  rw [h1, h2, Iso.inv_hom_id_assoc]
  rfl

variable (R) in
lemma etale_simplicial_chains_isZero_of_positive_degree (E : Spc) (k : ℤ) (hk : 0 < k) : IsZero (((chains R).obj E).X k) :=
  HomologicalComplex.isZero_extend_X _ _ _ (by rintro i (h : -(i:ℤ) = k); omega)

lemma sec_add {F G : Shv R} (f g : F ⟶ G) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
  map_add (secHom (G := G) U x) f g

lemma sec_comp {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem part0 {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (x : Sx E 0 U) : ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
  have hz : ((chains R).obj E).d (-((0:ℕ):ℤ)) (-((0:ℕ):ℤ) + 1) = 0 := (etale_simplicial_chains_isZero_of_positive_degree R E _ (by omega)).eq_of_tgt _ _
  have key : (chainsXIso R E 0).inv ≫ (δ n m α).v (-((0:ℕ):ℤ)) m (by simp) = ((chainsXIso R E 0).inv ≫ α.v (-((0:ℕ):ℤ)) n (by simp)) ≫ I.d n m := by
    rw [δ_v n m hm α _ _ (by simp) n (-((0:ℕ):ℤ) + 1) (by omega) rfl, hz]
    simp
  show Sec.map (_ ≫ _) _ = _
  rw [key]
  rfl

theorem partS {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) : ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  have key : (chainsXIso R E (p+1)).inv ≫ (δ n m α).v _ t ht = ((chainsXIso R E (p+1)).inv ≫ α.v _ s hs) ≫ I.d s t + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((free R).map (E.δ i) ≫ ((chainsXIso R E p).inv ≫ α.v (-(p:ℤ)) t (by omega))) := by
    rw [δ_v n m hm α _ _ ht s (-(p:ℤ)) (by omega) (by push_cast; ring), Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ← Category.assoc, chains_d]
    simp only [Category.assoc, Preadditive.sum_comp, Linear.smul_comp]
  show Sec.map (_ ≫ _) _ = _
  rw [key, Units.smul_def, Units.smul_def, sec_add, sec_zsmul, sec_sum]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [sec_zsmul, sec_comp, freeGen_map]
  rfl

end LateralTheory.EtaleFoundations.EvDeltaPf

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds : LateralTheory.EtaleFoundations.EtaleCochainEvaluationCoboundaryFormula := by
  intro R _ E I n m hm α U
  exact ⟨fun x => LateralTheory.EtaleFoundations.EvDeltaPf.part0 hm α U x,
    fun p s t hs ht x => LateralTheory.EtaleFoundations.EvDeltaPf.partS hm α U p s t hs ht x⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable (R : Type) [CommRing R]

noncomputable def psiOf (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift.{1} (P.obj U) => a U.unop x.down)
  naturality := by
    intro U V g
    refine ModuleCat.free_hom_ext (fun x => ?_)
    have := ha V.unop U.unop g.unop x.down
    simp [freeP] at this ⊢
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply]
    exact this.symm

theorem free_hom_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let ψ := psiOf R P F a ha
  let φ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj ((freeP R).obj P) ⟶ F :=
    ((sheafificationAdjunction _ _).homEquiv _ _).symm ψ
  have key : toSheafify _ ((freeP R).obj P) ≫ φ.hom = ψ := by
    have := ((sheafificationAdjunction _ _).homEquiv _ _).apply_symm_apply ψ
    rw [Adjunction.homEquiv_unit] at this
    exact this
  refine ⟨φ, fun U x => ?_⟩
  change ((toSheafify _ ((freeP R).obj P)).app (op U) ≫ φ.hom.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.comp_app, key]
  erw [ModuleCat.freeDesc_apply]
  rfl

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  intro R _ E I n a ha
  have hex : ∀ (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s), ∃ φ : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s,
      ∀ U x, Sec.map φ (freeGen R _ U x) = a p s h U x :=
    fun p s h => free_hom_exists R _ _ (a p s h) (fun V U g x => ha p s h V U g x)
  choose φ hφ using hex
  let f : ∀ (p : ℕ) (s : ℤ) (_ : -(p:ℤ) + n = s), (((chains R).obj E).X (-(p:ℤ)) ⟶ I.X s) :=
    fun p s h => (chainsXIso R E p).hom ≫ φ p s h
  let α : Cochain ((chains R).obj E) I n := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫ f (-i).toNat j (by omega)
    else 0)
  refine ⟨α, fun p s h U x => ?_⟩
  have gen : ∀ (q : ℕ) (hq : q = p) (e : -(p:ℤ) = -(q:ℤ)) (h' : -(q:ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
    rintro q rfl e h'
    simp
  have hv : α.v (-(p:ℤ)) s h = f p s h := by
    simp only [α, Cochain.mk_v]
    rw [dif_pos (by omega)]
    exact gen _ (by omega) _ _
  simp only [GlobalTheory.EtC.ev]
  rw [hv]
  simp only [f]
  rw [Iso.inv_hom_id_assoc]
  exact hφ p s h U x
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainsMayerVietorisShortExactOfFree
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleFreePresheafMayerVietorisShortExact : Prop :=
  ∀ (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g],
    Mono (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g))) ∧
    ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g)))
      (biprod.desc ((free R).map f) ((free R).map g)) w).Exact

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    ((chains R).map φ).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom =
      (chainsXIso R E p).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk p))) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := p) (i' := -(p:ℤ)) rfl
  have h2 : ((chains R).map φ).f (-(p:ℤ)) = (HomologicalComplex.extendMap ((chainsN R).map φ) ComplexShape.embeddingDownNat).f (-(p:ℤ)) := rfl
  rw [h2, h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i:ℤ) = n at h
  omega

theorem chainsXIso_nat' (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map φ).f (-(p : ℤ)) =
      (free R).map (φ.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← chainsXIso_nat, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem sq1 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    ((free R).map (pullbackObjIso f g (op (SimplexCategory.mk p))).inv ≫ (chainsXIso R (pullback f g) p).inv) ≫
      (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))).f (-(p:ℤ)) =
    biprod.lift ((free R).map (pullback.fst (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))))
        (-(free R).map (pullback.snd (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p))))) ≫
      (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) := by
  rw [← cancel_mono (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).hom]
  apply biprod.hom_ext
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_fst,
      biprod.map_fst, biprod.lift_fst_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_fst, chainsXIso_nat', ← Category.assoc, ← Functor.map_comp,
      pullbackObjIso_inv_comp_fst]
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_snd,
      biprod.map_snd, biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.comp_neg,
      chainsXIso_nat']
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    rw [← Category.assoc, ← Functor.map_comp, pullbackObjIso_inv_comp_snd]

theorem sq2 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) ≫
      (biprod.desc ((chains R).map f) ((chains R).map g)).f (-(p:ℤ)) =
    biprod.desc ((free R).map (f.app (op (SimplexCategory.mk p)))) ((free R).map (g.app (op (SimplexCategory.mk p)))) ≫
      (chainsXIso R E p).inv := by
  apply biprod.hom_ext'
  · have h1 : biprod.inl ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inl : (chains R).obj U ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inl_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inl_desc,
      chainsXIso_nat', biprod.inl_desc_assoc]
  · have h1 : biprod.inr ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inr : (chains R).obj V ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inr_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inr_desc,
      chainsXIso_nat', biprod.inr_desc_assoc]

theorem etale_chains_mayer_vietoris_short_exact_of_free (hfree : EtaleFreePresheafMayerVietorisShortExact) : EtaleMayerVietorisChainsShortExact := by
  intro R _ U V E f g hc
  obtain ⟨hf, hg, hep⟩ := hc
  have w : biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) ≫
      biprod.desc ((chains R).map f) ((chains R).map g) = 0 := by
    rw [biprod.lift_desc, ← Functor.map_comp, Preadditive.neg_comp, ← Functor.map_comp, pullback.condition]
    simp
  refine ⟨w, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : 0 < n
  · have h1 := chains_isZero R (pullback f g) n hn
    have h3 := chains_isZero R E n hn
    have h2 : IsZero ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n).obj
        ((chains R).obj U ⊞ (chains R).obj V)) :=
by
      have hU := chains_isZero R U n hn
      have hV := chains_isZero R V n hn
      refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso _ _ n)
      rw [IsZero.iff_id_eq_zero, ← biprod.total, hU.eq_of_tgt biprod.fst 0, hV.eq_of_tgt biprod.snd 0]
      simp
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h2) ?_ ?_
    · exact ⟨fun a b _ => h1.eq_of_tgt a b⟩
    · exact ⟨fun a b _ => h3.eq_of_src a b⟩
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
  obtain ⟨hmono, w', hex⟩ := hfree R (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))
  have hT := ShortComplex.ShortExact.mk' hex hmono (hep _)
  refine ShortComplex.shortExact_of_iso ?_ hT
  refine ShortComplex.isoMk ?e1 ?e2 ?e3 ?c1 ?c2
  case e1 =>
    refine ?_ ≪≫ (chainsXIso R _ p).symm
    exact (free R).mapIso (pullbackObjIso f g _).symm
  case e2 => exact biprod.mapIso (chainsXIso R U p).symm (chainsXIso R V p).symm ≪≫
      (HomologicalComplex.biprodXIso _ _ _).symm
  case e3 => exact (chainsXIso R E p).symm
  case c1 => exact sq1 R f g p
  case c2 => exact sq2 R f g p

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCochainCupAssocOfCupSpecAndAlexanderWhitney
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_cup_spec0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def t_aw_assoc0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M')
    (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w)
      (h3 : t + u = tu) (h4 : s + tu = w) a b c,
      ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
    ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
      (ab : Cochain ((chains R).obj E) M nm) (bc : Cochain ((chains R).obj E) M' mk)
      (x y : Cochain ((chains R).obj E) L w),
      μ.IsAW h1 α β ab → ν.IsAW h2 ab γ x → μ'.IsAW h3 β γ bc → ν'.IsAW h4 α bc y → x = y

theorem etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc (hs : t_cup_spec0) (ha : t_aw_assoc0) : EtaleCochainCupAssociativeOfPairing := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨ab, hab⟩ := (hs R μ (E := E) h1).1 α β
  rw [(hs R μ (E := E) h1).2 α β ab hab]
  obtain ⟨x, hx⟩ := (hs R ν (E := E) h2).1 ab γ
  rw [(hs R ν (E := E) h2).2 ab γ x hx]
  obtain ⟨bc, hbc⟩ := (hs R μ' (E := E) h3).1 β γ
  rw [(hs R μ' (E := E) h3).2 β γ bc hbc]
  obtain ⟨y, hy⟩ := (hs R ν' (E := E) h4).1 α bc
  rw [(hs R ν' (E := E) h4).2 α bc y hy]
  congr 1
  exact Subtype.ext (ha R μ ν μ' ν' hass E h1 h2 h3 h4 α.1 β.1 γ.1 ab.1 bc.1 x.1 y.1 hab hx hbc hy)

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCochainEvaluationNaturalInRestriction : Prop :=
  ∀ {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U),
    ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) = Sec.res g (ev α p s h U x)

def UnitClassExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ

def UnitClassUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ α β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) →
    (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev β.1 0 0 (by simp) U x = resGen 0 ζ) →
    CohomologyClass.mk α = CohomologyClass.mk β

def DegreeZeroCocyclePullback : Prop :=
  ∀ {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (α : Cocycle ((chains R).obj E') (res R F) 0),
    ∃ β : Cocycle ((chains R).obj E) (res R F) 0, pull R f F 0 (CohomologyClass.mk α) = CohomologyClass.mk β ∧
      ∀ (U : Scheme.{0}) (x : Sx E 0 U),
        ev β.1 0 0 (by simp) U x = ev α.1 0 0 (by simp) U ((f.app (op (SimplexCategory.mk 0))).app (op U) x)

theorem freeGen_nat {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up (P.map g.op x)) := by
    simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]; erw [ModuleCat.free_map_apply]; rfl
  exact h.symm.trans (congrArg (toSheafify Scheme.etaleTopology ((freeP R).obj P) |>.app (op V)).hom hm)

theorem ev_nat_pf : EtaleCochainEvaluationNaturalInRestriction := by
  intro R _ E I n α p s h V U g x
  unfold ev
  rw [← freeGen_nat]
  have key := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at key
  exact key

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCohomologyOperationCompOfImageSpec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSemilinearCohomologyOperationImageSpec : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

namespace OpCompPf

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

noncomputable def invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat {V U} g s a := by
    apply (hb V s).1
    have h1 := ρ.nat g s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app V s ((AddEquiv.ofBijective (ρ.app V s) (hb V s)).symm (Sec.res g a)) = Sec.res g a :=
      (AddEquiv.ofBijective (ρ.app V s) (hb V s)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [h3, ← h1, h2]
  comm U s t a := by
    apply (hb U t).1
    have h1 := ρ.comm U s t ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a)) = Sec.map (J.d s t) a :=
      (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [h3, ← h1, h2]

theorem invMap_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (J.X s) U) :
    ρ.app U s ((invMap ρ hb).app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a

theorem app_invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invMap ρ hb).app U s (ρ.app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

end OpCompPf

open OpCompPf in
theorem etale_cohomology_operation_comp_of_image_spec (hspec : EtaleSemilinearCohomologyOperationImageSpec) : EtaleCochainSemilinearMapCompCompatible := by
  intro S R _ _ I J J' ρ ρ' u hu
  constructor
  · intro E n x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
    rw [(hspec S R ρ).2 E n α β hβ, cpost_mk]
    apply (hspec S R ρ').2
    intro p s h U y
    show ev (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom, hβ p s h U y, hu]
  · intro hb E n
    let σ := invMap ρ hb
    rw [Function.bijective_iff_has_inverse]
    refine ⟨σ.op.app E n, ?_, ?_⟩
    · intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
      rw [(hspec S R ρ).2 E n α β hβ]
      apply (hspec R S σ).2
      intro p s h U y
      rw [hβ p s h U y]
      exact (app_invMap ρ hb U s _).symm
    · intro x
      obtain ⟨β, rfl⟩ := x.mk_surjective
      obtain ⟨γ, hγ⟩ := (hspec R S σ).1 E n β
      rw [(hspec R S σ).2 E n β γ hγ]
      apply (hspec S R ρ).2
      intro p s h U y
      rw [hγ p s h U y]
      exact (invMap_app ρ hb U s _).symm

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupCompatibleWithCoefficientMapsOfSpec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCupCompatAlexanderWhitneyCocycleSpec : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

theorem etale_cochain_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (add_zero n) (-(p : ℤ)) s s h (add_zero s), Cochain.ofHom_v]
  rfl

theorem etale_cocycle_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (zcomp α (Cocycle.ofHom m) (add_zero n)).1 p s h U x = Sec.map (m.f s) (ev α.1 p s h U x) :=
  etale_cochain_comp_hom_evaluation_eq_map m α.1 p s h U x

theorem etale_cup_compatible_with_coefficient_maps_of_spec (hspec : EtaleCupCompatAlexanderWhitneyCocycleSpec) : EtaleCupProductNaturalInCoefficients := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, hγ⟩ := (hspec R μ hk).1 α β
  rw [(hspec R μ hk).2 α β γ hγ, cpost_mk, cpost_mk, cpost_mk]
  symm
  apply (hspec R ν hk).2
  intro N w h U x
  rw [etale_cocycle_comp_hom_evaluation_eq_map, hγ N w h U x]
  simp only [Sec.map]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, etale_cocycle_comp_hom_evaluation_eq_map, etale_cocycle_comp_hom_evaluation_eq_map]
  congr 1
  exact hc U _ _ w _ _ _

end LateralTheory.EtaleFoundations
end

