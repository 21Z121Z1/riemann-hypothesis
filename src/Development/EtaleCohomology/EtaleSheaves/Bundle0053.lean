import Development.EtaleCohomology.EtaleSheaves.Bundle0034
import Development.EtaleCohomology.EtaleSheaves.Bundle0038
import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Development.EtaleCohomology.TateTwists.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.Bundle0042

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwTrivPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.TwistTrivial

theorem genRes {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (((Scheme.Γ ⋙ twF q i).map g.op).hom _) = _
  congr 1
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

theorem prim_map_comp {q : ℕ} {X Y S : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) (f : Y ⟶ X) :
    (ζ.map s.appTop.hom).map f.appTop.hom = ζ.map (f ≫ s).appTop.hom := by
  apply Subtype.ext
  change f.appTop.hom (s.appTop.hom ζ.1) = (f ≫ s).appTop.hom ζ.1
  rw [Scheme.Hom.comp_appTop]
  rfl

def Mul : Prop := ∀ (q : ℕ), ∃ μ : ∀ (j k l : ℤ), j + k = l → ∀ (X : Scheme.{0}), Sec (tw q k) X → (Sec (tw q j) X →+ Sec (tw q l) X),
  (∀ (j k l : ℤ) (h : j + k = l) {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Sec (tw q k) X) (x : Sec (tw q j) X),
      Sec.res f (μ j k l h X y x) = μ j k l h Y (Sec.res f y) (Sec.res f x)) ∧
  (∀ (j k l k' : ℤ) (h : j + k = l) (h' : l + k' = j) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X),
      μ l k' j h' X (twGen k' ζ) (μ j k l h X (twGen k ζ) x) = x)

theorem TwTriv_of (hM : Mul) : LateralTheory.E.LCIsoPf.TwTriv := by
  intro q i S ζ
  obtain ⟨μ, hnat, hcan⟩ := hM q
  refine ⟨fun X s => AddEquiv.mk' ⟨μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom)),
      μ i (-i) 0 (add_neg_cancel i) X (twGen (-i) (ζ.map s.appTop.hom)),
      fun x => hcan 0 i i (-i) (zero_add i) (add_neg_cancel i) X _ x,
      fun y => hcan i (-i) 0 i (add_neg_cancel i) (zero_add i) X _ y⟩ (fun a b => map_add (μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom))) a b), ?_⟩
  intro X Y s t f hf x
  change Sec.res f (μ 0 i i _ X _ x) = μ 0 i i _ Y _ (Sec.res f x)
  rw [hnat, genRes, prim_map_comp, hf]

end LateralTheory.E.TwistTrivial
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwistGenerators
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf

def LeafTwGenIndep : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen 0 ζ = twGen 0 ξ

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map (Scheme.Γ.map g.op).hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun t => t.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom y) ?_)
  exact congrArg (Submodule.Quotient.mk (p := twRel q i Γ(V, ⊤))) (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom))

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (k : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res k x) = Sec.res (h ≫ k) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  show (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, F.obj.map_id]
  rfl

theorem tw_isSheafFor (q : ℕ) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) :
    Presieve.IsSheafFor ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology (tw q 0).obj
    (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))).1 (tw q 0).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact hF S hS

section Glue

def cov (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sieve U := Classical.choose (hP q U hU)

theorem cov_mem (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : cov hP q U hU ∈ Scheme.etaleTopology U :=
  (Classical.choose_spec (hP q U hU)).1

theorem cov_prim (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (V : Scheme.{0}) (g : V ⟶ U) (hg : (cov hP q U hU).arrows g) :
    Nonempty (Prim q Γ(V, ⊤)) :=
  (Classical.choose_spec (hP q U hU)).2 V g hg

def fam (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) :
    Presieve.FamilyOfElements ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) (cov hP q U hU).arrows :=
  fun V g hg => twGen 0 (Classical.choice (cov_prim hP q U hU V g hg))

theorem fam_compat (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : (fam hP q U hU).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  change _ = Sec.res g (twGen 0 _)
  rw [twGen_res]
  exact hI q Z _ _

def one (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sec (tw q 0) U :=
  (tw_isSheafFor q U _ (cov_mem hP q U hU)).amalgamate (fam hP q U hU) (fam_compat hP hI q U hU)

theorem one_char (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (W : Scheme.{0}) (k : W ⟶ U) (ζ : Prim q Γ(W, ⊤)) :
    Sec.res k (one hP hI q U hU) = twGen 0 ζ := by
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) W ((cov hP q U hU).pullback k)
    (Scheme.etaleTopology.pullback_stable k (cov_mem hP q U hU)) _ _ fun V h hh => ?_
  rw [res_comp, twGen_res]
  have hv := (tw_isSheafFor q U _ (cov_mem hP q U hU)).valid_glue (fam_compat hP hI q U hU) (h ≫ k) hh
  refine hv.trans ?_
  exact hI q V _ _

end Glue

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec := by
  intro q _
  refine ⟨one hP hI q, fun V U g hU hV => ?_, fun U hU ζ => ?_⟩
  · refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) V (cov hP q V hV) (cov_mem hP q V hV) _ _ fun W h hh => ?_
    obtain ⟨ζ⟩ := cov_prim hP q V hV W h hh
    rw [res_comp, one_char hP hI q U hU W _ ζ, one_char hP hI q V hV W h ζ]
  · rw [← one_char hP hI q U hU U (𝟙 U) ζ, res_id]

end LateralTheory.E.LeafUnitSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.WeightBoundsExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib LateralTheory.E.LeafHtpyAWPf

namespace LateralTheory.E.FreeSheafGeneratorLifts
section Lift
variable {R : Type} [CommRing R]

def freeLiftP (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift (P.obj U) => f U.unop x.down)
  naturality {U V} g := by
    refine ModuleCat.free_hom_ext fun x => ?_
    obtain ⟨x⟩ := x
    have h1 : (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      exact Finsupp.mapDomain_single
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk _)) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk _))
    rw [h1]
    erw [ ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (hf g.unop x).symm

def freeLift (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (free R).obj P ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property⟩

theorem freeLift_gen (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((freeLift P G f hf).hom.app (op U)).hom (freeGen R P U x) = f U x := by
  have := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property)
  exact this.trans (ModuleCat.freeDesc_apply (R := ULift.{1} R) _ _)

theorem freeGen_nat (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res (F := (free R).obj P) g (freeGen R P U x) := by
  have h1 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (P.map g.op x)) := by
    simp [freeP, ModuleCat.freeMk, ModuleCat.free]
    exact Finsupp.mapDomain_single
  have h2 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  unfold freeGen
  erw [← h1]
  exact h2

theorem ev_nat {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) = Sec.res g (ev α p s h U x) := by
  unfold ev
  rw [freeGen_nat]
  exact congrArg (fun φ => φ.hom (freeGen R _ U x)) (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)

theorem sub_nat {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((E.obj (op (SimplexCategory.mk N))).map g.op x) j l h =
      (E.obj (op (SimplexCategory.mk l))).map g.op (Sx.sub x j l h) :=
  NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

variable {K : Cx R} {E : Spc} {k : ℤ}
  (F : ∀ (N : ℕ) (w : ℤ), -(N : ℤ) + k = w → ∀ U : Scheme.{0}, Sx E N U → Sec (K.X w) U)
  (hF : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U),
    Sec.res g (F N w h U x) = F N w h V ((E.obj (op (SimplexCategory.mk N))).map g.op x))

def comp (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) : ((chains R).obj E).X (-(N : ℤ)) ⟶ K.X w :=
  (chainsXIso R E N).hom ≫ freeLift _ (K.X w) (F N w h) (fun g x => hF N w h g x)

theorem comp_cast (N N' : ℕ) (e : N' = N) (hp : -(N : ℤ) = -(N' : ℤ)) (w : ℤ) (h : -(N : ℤ) + k = w)
    (h' : -(N' : ℤ) + k = w) :
    (((chains R).obj E).XIsoOfEq hp).hom ≫ comp F hF N' w h' = comp F hF N w h := by
  subst e
  simp

include hF in

theorem exists_cochain : ∃ η : Cochain ((chains R).obj E) K k,
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w h U x = F N w h U x := by
  refine ⟨Cochain.mk fun p q hpq => if hp : p ≤ 0 then
    (((chains R).obj E).XIsoOfEq (by omega : p = -(((-p).toNat : ℕ) : ℤ))).hom ≫ comp F hF (-p).toNat q (by omega)
    else 0, fun N w h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, dif_pos (by omega), comp_cast F hF N _ (by omega) _ w h, comp, Iso.inv_hom_id_assoc]
  exact freeLift_gen _ _ _ _ U x

end Lift

end LateralTheory.E.FreeSheafGeneratorLifts

open LateralTheory.E.FreeSheafGeneratorLifts in
theorem LateralTheory.E.LeafHtpyAWPf.LeafHAWExists_of : LateralTheory.E.LeafHtpyAWPf.LeafHAWExists := by
  intro R _ I J K h hnat E n m k hk α β
  refine exists_cochain (fun N w hw U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow •
    h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))) ?_
  intro N w hw V U g x
  show ((K.X w).obj.map g.op).hom _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, Units.smul_def, sub_nat, sub_nat, FreeSheafGeneratorLifts.ev_nat, FreeSheafGeneratorLifts.ev_nat, ← hnat]

namespace LateralTheory.E.FreeSheafGeneratorLifts
section
variable {R : Type} [CommRing R] {I J K : Cx R}

theorem htpy' (μ μ' : Pair I J K) (H : HFam R I J K)
    (hH : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (H U s t (w - 1) (by omega) a b) +
        H U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • H U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b))
    (U : Scheme.{0}) (s t w0 w s' t' : ℤ) (h : s + t = w) (h0 : s + t = w0 + 1)
    (hs : s + 1 = s') (ht : t + 1 = t') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w0 w) (H U s t w0 h0 a b) = μ.mul U s t w h a b - μ'.mul U s t w h a b
      - H U s' t w (by omega) (Sec.map (I.d s s') a) b - s.negOnePow • H U s t' w (by omega) a (Sec.map (J.d t t') b) := by
  obtain rfl : w0 = w - 1 := by omega
  subst hs ht
  rw [hH U s t w h a b]
  abel

theorem hmul_bd_left (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    H U s t w h (bd f p y) b = bd (fun q z => H U s t w h (f q z) b) p y :=
  bd_map (((H U s t w h).flip b).toAddMonoidHom) f p y

theorem hmul_bd_right (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    H U s t w h a (bd f p y) = bd (fun q z => H U s t w h a (f q z)) p y :=
  bd_map ((H U s t w h a).toAddMonoidHom) f p y

theorem hmul_congr (H : HFam R I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w + 1) (h' : s' + t' = w + 1) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    H U s t w h (ev α p s hs U y) (ev β q t ht U z) = H U s' t' w h' (ev α p s' hs' U y) (ev β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

def Fh (H : HFam R I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w + 1 then H U _ _ w hh (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

end

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x := by
  have := ev_add (a - b) b p s h U x
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem d_cocycle {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ)
    (s s' : ℤ) (hs : -(p : ℤ) + n = s) (hs' : -(p : ℤ) + (n + 1) = s') (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s s') (ev α.1 p s hs U y) =
      -((n + 1).negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = s' then ev α.1 q s' hh U z else 0) p y) := by
  have h0 := ev_delta_bd rfl α.1 p s s' hs hs' U y
  rw [(Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2] at h0
  have hz : ev (0 : Cochain ((chains R).obj E) I (n + 1)) p s' hs' U y = 0 := by
    rw [ev_eq, Cochain.zero_v, Limits.comp_zero]; rfl
  rw [hz] at h0
  exact eq_neg_of_add_eq_zero_left h0.symm

theorem recH {G : Type*} [AddCommGroup G] (X Y P P' Q Q' : G) (ε A s B K c' c e : ℤ) (hP : P' = P) (hQ : Q' = Q)
    (h1 : K * c' = -(ε * A)) (h2 : K * (c * e) = -(ε * (s * B))) :
    ε • (X - Y - -(A • P) - s • -(B • Q)) + K • (c' • P' + c • e • Q') = ε • X - ε • Y := by
  rw [hP, hQ]
  have : K • (c' • P + c • e • Q) = (K * c') • P + (K * (c * e)) • Q := by
    simp only [smul_add, smul_smul]
  rw [this, h1, h2]
  simp only [smul_sub, smul_neg, smul_smul, neg_smul]
  abel

theorem LeafHAWBounds_proved : LeafHAWBounds := by
  intro R _ I J K μ μ' H hH E n m k hk α β γ₁ γ₂ h1 h2 c hc
  apply ev_ext
  intro N w hw U x
  rw [ev_sub', ev_delta_bd (by omega : k - 1 + 1 = k) c N (-(N : ℤ) + (k - 1)) w rfl hw U x, hc N _ rfl U x, h1 N w hw U x, h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fh H α.1 β.1 U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dif_pos (by omega), hc N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fh
    rw [dif_pos (by omega)]
  rw [bd_aw (Fh H α.1 β.1 U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, htpy' μ μ' H hH U _ _ _ w (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) (by omega) (by omega) (by omega) (by omega)]
  rw [d_cocycle α p (-((p : ℕ) : ℤ) + n) _ rfl (by omega) U, d_cocycle β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl (by omega) U]
  simp only [map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply, Units.smul_def, hmul_bd_left, hmul_bd_right]
  refine recH _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-1, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨(p : ℤ) - 1, by ring⟩

theorem LeafHtpyAW_proved : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := by
  intro R _ I J K μ μ' ⟨h, hnat, hht⟩ E n m k hk α β γ γ' h₁ h₂
  obtain ⟨η, hη⟩ := LeafHAWExists_of R h hnat E hk α.1 β.1
  have hc := LeafHAWBounds_proved R μ μ' h hht E hk α β γ γ' h₁ h₂ η hη
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨k - 1, by omega, η, by rw [hc]; rfl⟩

end LateralTheory.E.FreeSheafGeneratorLifts
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.inclPf
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.inclPf

universe v u

set_option linter.dupNamespace false in
abbrev E (M : ℤ) := ComplexShape.embeddingUpIntGE M

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (M : ℤ)

lemma xiso_indep {i j : ℕ} {p : ℤ} (hi : (E M).f i = p) (hj : (E M).f j = p) :
    K.stupidTruncXIso (E M) hi = K.stupidTruncXIso (E M) hj := by
  obtain rfl : i = j := (E M).injective_f (hi.trans hj.symm)
  rfl

lemma trd (i j : ℕ) :
    (K.stupidTrunc (E M)).d ((E M).f i) ((E M).f j) ≫ (K.stupidTruncXIso (E M) (i := j) rfl).hom =
      (K.stupidTruncXIso (E M) (i := i) rfl).hom ≫ K.d ((E M).f i) ((E M).f j) := by
  simp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.extend_d_eq _ _ rfl rfl, HomologicalComplex.restriction]
  erw [eqToIso_refl, eqToIso_refl]; simp

open Classical in

def iotaf (p : ℤ) : (K.stupidTrunc (E M)).X p ⟶ K.X p :=
  if h : ∃ i, (E M).f i = p then (K.stupidTruncXIso (E M) h.choose_spec).hom else 0

lemma iotaf_eq (i : ℕ) : iotaf K M ((E M).f i) = (K.stupidTruncXIso (E M) (i := i) rfl).hom := by
  have h : ∃ j, (E M).f j = (E M).f i := ⟨i, rfl⟩
  rw [iotaf, dif_pos h, xiso_indep K M h.choose_spec rfl]

lemma stupidTruncation_GE_isZero_below_bound (p : ℤ) (hp : p < M) : IsZero ((K.stupidTrunc (E M)).X p) :=
  HomologicalComplex.isZero_stupidTrunc_X _ _ _ (fun i h => by simp [E] at h; omega)

lemma mem (p : ℤ) (hp : M ≤ p) : (E M).f (p - M).toNat = p := by simp [E]; omega

def iota : K.stupidTrunc (E M) ⟶ K where
  f := iotaf K M
  comm' p q hpq := by
    simp only [ComplexShape.up_Rel] at hpq
    by_cases hp : M ≤ p
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, (E M).f j = q := ⟨i + 1, by simp [E] at hpq ⊢; omega⟩
      rw [iotaf_eq, iotaf_eq]
      exact (trd K M i j).symm
    · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _

lemma iota_iso (p : ℤ) (hp : M ≤ p) : IsIso ((iota K M).f p) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
  show IsIso (iotaf K M _)
  rw [iotaf_eq]; infer_instance

lemma iota_nat {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (E M) ≫ iota L M = iota K M ≫ g := by
  ext p
  simp only [HomologicalComplex.comp_f]
  by_cases hp : M ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
    show _ ≫ iotaf L M _ = iotaf K M _ ≫ _
    rw [iotaf_eq, iotaf_eq]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom _ _ rfl
  · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _
end

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {A B I : CochainComplex C ℤ} (φ : A ⟶ B) (M : ℤ)

def P (m : ℤ) (c : Cochain B I m) : Cochain A I m := (Cochain.ofHom φ).comp c (zero_add m)

lemma precomp_injective [I.IsStrictlyGE 0] (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (m : ℤ) (hm : m + M ≤ 0) :
    Function.Injective (P (I := I) φ m) := by
  intro c c' h
  ext p q hpq
  by_cases hp : M ≤ p
  · have := hiso p hp
    have h' := congrArg (fun x : Cochain A I m => x.v p q hpq) h
    simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h'
    exact (cancel_epi _).1 h'
  · exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _

lemma precomp_surjective₂ (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (hz : ∀ p, p < M → IsZero (A.X p)) (m : ℤ) :
    Function.Surjective (P (I := I) φ m) := by
  intro d
  refine ⟨Cochain.mk (fun p q hpq => if h : M ≤ p then (haveI := hiso p h; inv (φ.f p)) ≫ d.v p q hpq else 0), ?_⟩
  ext p q hpq
  simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  by_cases hp : M ≤ p
  · rw [dif_pos hp]; simp
  · exact (hz p (by omega)).eq_of_src _ _
end

section
variable {R : Type} [CommRing R] {A B I : Cx R} (φ : A ⟶ B)

lemma cpull_mk (n : ℤ) (z : Cocycle B I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (Cocycle.mk (P φ n z) (n + 1) rfl
      (by simp [P, Cocycle.δ_eq_zero])) := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1

lemma cpull_bij [I.IsStrictlyGE 0] (M : ℤ) (hiso : ∀ p, M ≤ p → IsIso (φ.f p))
    (hz : ∀ p, p < M → IsZero (A.X p)) (n : ℤ) (hn : n + 1 + M ≤ 0) :
    Function.Bijective (cpull φ I n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := precomp_surjective₂ φ M hiso hz (n - 1) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨β', precomp_injective φ M hiso n (by omega) ?_⟩
    rw [Cocycle.mk_coe] at hβ
    rw [← hβ, P, P, δ_ofHom_comp]
  · intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨c, hc⟩ := precomp_surjective₂ φ M hiso hz n (z : Cochain A I n)
    have hδ : δ n (n + 1) c = 0 := by
      apply precomp_injective φ M hiso (n + 1) (by omega)
      have : P φ (n + 1) (δ n (n + 1) c) = δ n (n + 1) (P φ n c) := by simp [P]
      rw [this, hc, Cocycle.δ_eq_zero]; simp [P]
    refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl hδ), ?_⟩
    rw [cpull_mk]
    congr 1
    apply Cocycle.ext
    simp only [Cocycle.mk_coe]
    exact hc
end

theorem incl_of : LateralTheory.E.stupidPf.incl := by
  intro R _ I _ K L g N
  refine ⟨iota K (-(N : ℤ)), iota L (-(N : ℤ)), iota_nat _ g, fun n hn => ⟨?_, ?_⟩⟩
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso K _) (stupidTruncation_GE_isZero_below_bound K _) n (by omega)
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso L _) (stupidTruncation_GE_isZero_below_bound L _) n (by omega)

end LateralTheory.E.inclPf
end
end

