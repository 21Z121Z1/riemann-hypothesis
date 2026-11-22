import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MapSeqIndAll
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def castV {A B : HLat K} (h : A = B) : A.V ≃ₗ[K] B.V := by
  subst h
  exact LinearEquiv.refl K A.V

def unitLat (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) : HLat K :=
  HLat.ofCoord (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))) fun _ => 1

theorem ofCoord_good {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ}
    (hL : Submodule.IsLattice K L) (hX : ∀ v, IsUnit (X v).det) : (HLat.ofCoord L X).Good :=
  ⟨hX, hL.fg, hL.span_eq_top⟩

theorem unitLat_good (n : ℕ) : (unitLat K n).Good :=
  ⟨fun _ => by
      show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
      rw [Matrix.det_one]; exact isUnit_one,
    Submodule.fg_span (Set.finite_range _),
    (Submodule.span_span_of_tower (𝓞 K) K (Set.range (Pi.basisFun K (Fin n)))).trans (Pi.basisFun K (Fin n)).span_eq⟩

def unitMap (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    (unitLat K (Module.finrank ℂ W)).V →ₛₗ[σ] W :=
  (lin (stdOrthonormalBasis ℂ W)).comp (cptL σ (Module.finrank ℂ W))

theorem unitMap_b (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (k : Fin (Module.finrank ℂ W)) :
    unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k) = stdOrthonormalBasis ℂ W k := by
  have h : cptL σ (Module.finrank ℂ W) (Pi.basisFun K _ k) = Pi.single k 1 := by
    funext i
    by_cases hi : i = k <;> simp [cptL, cpt, hi]
  exact (congrArg (lin (stdOrthonormalBasis ℂ W)) h).trans (lin_single _ k)

theorem unitMap_basis (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    LinearIndependent ℂ (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) ∧
      Submodule.span ℂ (Set.range fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = ⊤ := by
  have h : (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = (stdOrthonormalBasis ℂ W).toBasis :=
    funext fun k => unitMap_b σ W k
  rw [h]
  exact ⟨(stdOrthonormalBasis ℂ W).toBasis.linearIndependent, (stdOrthonormalBasis ℂ W).toBasis.span_eq⟩

theorem hLatTie_castV {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ} {A : HLat K}
    (h : HLat.ofCoord L X = A) : HLatTie A L X (castV h) := by
  subst h
  exact ⟨(Submodule.map_id L).symm, fun _ _ _ => rfl⟩

variable {m : ℕ} {d : Fin m → ℕ} (M : ∀ i, Submodule (𝓞 K) (Fin (d i) → K))
  (X : ∀ i, InfinitePlace K → Matrix (Fin (d i)) (Fin (d i)) ℂ)
  (W : ℕ → Type) [∀ j, NormedAddCommGroup (W j)] [∀ j, InnerProductSpace ℂ (W j)] [∀ j, FiniteDimensional ℂ (W j)]

def latSeq : ℕ → HLat K
  | 0 => unitLat K (Module.finrank ℂ (W 0))
  | j + 1 => if h : j < m then HLat.ofCoord (M ⟨j, h⟩) (X ⟨j, h⟩) else unitLat K (Module.finrank ℂ (W (j + 1)))

theorem latSeq_succ (i : Fin m) : latSeq M X W ((i : ℕ) + 1) = HLat.ofCoord (M i) (X i) := dif_pos i.2

theorem latSeq_off {j : ℕ} (h : j = 0 ∨ m < j) : latSeq M X W j = unitLat K (Module.finrank ℂ (W j)) := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

variable {σ : K →+* ℂ} (f : ∀ i : Fin m, (Fin (d i) → K) →ₛₗ[σ] W ((i : ℕ) + 1))

def mapSeq : ∀ j, (latSeq M X W j).V →ₛₗ[σ] W j
  | 0 => unitMap σ (W 0)
  | j + 1 =>
    if h : j < m then (f ⟨j, h⟩).comp (castV (latSeq_succ M X W ⟨j, h⟩)).toLinearMap
    else (unitMap σ (W (j + 1))).comp (castV (latSeq_off M X W (Or.inr (Nat.lt_succ_of_le (Nat.le_of_not_lt h))))).toLinearMap

theorem mapSeq_succ (i : Fin m) :
    mapSeq M X W f ((i : ℕ) + 1) = (f i).comp (castV (latSeq_succ M X W i)).toLinearMap := dif_pos i.2

theorem mapSeq_off {j : ℕ} (h : j = 0 ∨ m < j) :
    mapSeq M X W f j = (unitMap σ (W j)).comp (castV (latSeq_off M X W h)).toLinearMap := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

theorem castV_ind {H : Type} [AddCommGroup H] [Module ℂ H] (P : ∀ A : HLat K, (A.V →ₛₗ[σ] H) → Prop) {A B : HLat K} (h : A = B)
    {g : B.V →ₛₗ[σ] H} (hg : P B g) : P A (g.comp (castV h).toLinearMap) := by
  subst h
  exact hg

theorem mapSeq_ind (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [mapSeq_succ]
  exact castV_ind (P _) _ (hP i)

theorem mapSeq_ind_all (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i))
    (h0 : ∀ j, P j (unitLat K (Module.finrank ℂ (W j))) (unitMap σ (W j))) (j : ℕ) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  by_cases h : j = 0 ∨ m < j
  · rw [mapSeq_off M X W f h]
    exact castV_ind (P _) _ (h0 j)
  · exact mapSeq_ind M X W f P hP j (by omega) (by omega)

theorem map_castV {H : ℕ → HLat K} {g : ∀ j, (H j).V →ₛₗ[σ] W j} (hH : H = latSeq M X W) (hg : HEq g (mapSeq M X W f))
    (i : Fin m) (h : HLat.ofCoord (M i) (X i) = H ((i : ℕ) + 1)) (x : Fin (d i) → K) :
    g ((i : ℕ) + 1) (castV h x) = f i x := by
  subst hH
  obtain rfl := eq_of_heq hg
  rw [mapSeq_succ]
  have key : ∀ {A B : HLat K} (h : A = B) (h' : B = A) (y : A.V), castV h' (castV h y) = y := by
    intro A B h h' y
    subst h
    rfl
  exact congrArg (f i) (key h _ x)

end Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

open MjCoord

def mjLat (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ℕ → HLat D.what₂.LL :=
  latSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj

def mjH (_Z : ReadL R F X0 Y) (j : ℕ) : HLat D.what₂.LL := mjLat R F j

def jM (Z : ReadL R F X0 Y) (j : ℕ) : (mjH Z j).V →ₛₗ[D.what₂.embLL] D.what₂.Mj j :=
  mapSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj Z.jW j

variable (Z : ReadL R F X0 Y)

theorem mjH_succ (i : Fin D.R.m) : mjH Z ((i : ℕ) + 1) = HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i) :=
  latSeq_succ _ _ _ i

theorem mjH_off {j : ℕ} (h : j = 0 ∨ D.R.m < j) : mjH Z j = unitLat D.what₂.LL (Module.finrank ℂ (D.what₂.Mj j)) :=
  latSeq_off _ _ _ h

def mjCoord (i : Fin D.R.m) : (Fin ((s0Of R F).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (mjH Z ((i : ℕ) + 1)).V :=
  castV (mjH_succ Z i).symm

theorem mjH_good (hH : Holds R F) (j : ℕ) : (mjH Z j).Good :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW (fun _ A _ => A.Good)
    (fun i => ofCoord_good (hH.prim.mLat i) fun v => frame_gram_unit _ (RealDat3.kForm_of (F := F) hH.prim.unif false i v).1)
    (fun _ => unitLat_good _) j

theorem jM_basis (hH : Holds R F) (j : ℕ) : LinearIndependent ℂ (fun k => jM Z j ((mjH Z j).b k)) ∧
    Submodule.span ℂ (Set.range fun k => jM Z j ((mjH Z j).b k)) = ⊤ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => LinearIndependent ℂ (fun k => g (A.b k)) ∧ Submodule.span ℂ (Set.range fun k => g (A.b k)) = ⊤)
    (fun i => by
      have h : (fun k => Z.jW i ((HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i)).b k)) = fun k => Z.jW i (Pi.single k 1) :=
        funext fun k => congrArg (Z.jW i) (Pi.basisFun_apply _ _ k)
      exact h ▸ jW_basis Z hH i)
    (fun _ => unitMap_basis _ _) j

theorem jM_lat (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    x ∈ (mjH Z j).L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      jM Z j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun j A g => ∀ x : A.V, x ∈ A.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      g x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v)
    (fun i => (jW_lat Z hP hH i).2) j h1 h2 x

theorem mjLat_sub (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range (jM Z j) :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW (fun j _ g => ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range g)
    (fun i => (jW_lat Z hP hH i).1) j h1 h2

theorem jM_metric (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => jW_norm Z hH i) j h1 h2 x

def mjIds (Xd : DivX D) (h : Xd.MjH = mjH Z) : MjHIds D A3.A Xd (A3.indefDown (s0Of R F)) where
  eW i := castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem mjHTie_of_eq (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW (mjIds Z Xd h) where
  j_eq i x := map_castV _ _ D.what₂.Mj Z.jW h hj i _ x
  hlat i := hLatTie_castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem exists_mjHTie (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    ∃ JM, MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM :=
  ⟨_, mjHTie_of_eq Z Xd h hj⟩

def withMj (hP : Pins R F cG) (hH : Holds R F) (Xd : DivX D)
    (iM : ∀ j c, (mjH Z j).V →ₗ[D.what₂.LL] Xd.geo.Fn (Xd.Yv j c))
    (hiM : ∀ j c x, iM j c x ∈ Xd.geo.H0 (Xd.Yv j c) (Xd.Lw j c (DV.kapW D j))) : DivX D :=
  { Xd with
    MjH := mjH Z
    MjH_good := mjH_good Z hH
    jM := jM Z
    jM_basis := jM_basis Z hH
    jM_lat := jM_lat Z hP hH
    MjLat_sub := mjLat_sub Z hP hH
    jM_metric := jM_metric Z hH
    iMj := iM
    iMj_mem := hiM }

theorem mjHTie_withMj (hP : Pins R F cG) (hH : Holds R F) (Xd : DivX D)
    (iM : ∀ j c, (mjH Z j).V →ₗ[D.what₂.LL] Xd.geo.Fn (Xd.Yv j c))
    (hiM : ∀ j c x, iM j c x ∈ Xd.geo.H0 (Xd.Yv j c) (Xd.Lw j c (DV.kapW D j))) :
    MjHTie D A3.A (withMj Z hP hH Xd iM hiM) (A3.indefDown (s0Of R F)) Z.jW (mjIds Z _ rfl) :=
  mjHTie_of_eq Z _ rfl HEq.rfl

section Reface

variable {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {kap : ℝ} {lam : type_of% R.lam3} {err : type_of% (R.updS kap lam).err0}
  {Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}
  (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y')

end Reface

example : Module.finrank ℚ (unitLat ℚ 1).V = 1 := Module.finrank_fin_fun ℚ

example : Subsingleton (unitLat ℚ 0).V := inferInstanceAs (Subsingleton (Fin 0 → ℚ))

example (M : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) : Module.finrank ℚ
    (latSeq (m := 1) (d := fun _ => 3) (fun _ => M) (fun _ _ => 1) (fun _ => ℂ) 1).V = 3 := Module.finrank_fin_fun ℚ

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Wp3ApplyEqSqMulSubSqMul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section General

variable {D : D7} {A : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Parts (R : RealDat3 D A Ks) : Type :=
  (A.fam3.base3.Ix → Submodule ℂ R.HE.H) × (LevelP R.Pg D.R.r ℂ → Submodule ℂ (MMap (R.MY 0))) ×
    ∀ i : Fin D.R.m, A.fam3.base3.Ix → Submodule ℂ (R.HW i (sg0 D A.A)).H

def cxW (R : RealDat3 D A Ks) (F : Face3 D A) (u : Parts R) : Cx.CxData A.fam3.amb3 :=
  { R.toCx3 F with
    EEp := fun p => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) (u.1 p)) :))
    EEl := fun c => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) ((u.2.1 (R.toRealDat.levR F.lv2 c)).comap R.HE.e)) :))
    Wp := fun i p => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) (u.2.2 i p)) :)) }

def carriesW (R : RealDat3 D A Ks) (E : type_of% R.EEc) (p : A.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ) : Prop :=
  E c ≠ ⊥ ∧ (E c).map (LinearMap.adjoint (R.Th A.A.μ0)) ≤
    Submodule.span ℂ (R.jX A.A.μ0 '' ((A.rowI A.A.μ0).inertTypeEigenspaceSum p.1 : Set (A.A.fam.R A.A.μ0).S.Forms))

def trSemW (R : RealDat3 D A Ks) (F : Face3 D A) (u : type_of% R.Carries × type_of% R.Wc')
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ j p c, u.1 p c → ∀ s : (A.liftI j A.A.μ0).OpIx → D.what₂.LL,
    (∃ x : (A.A.fam.L j A.A.μ0).S.Forms, x ∈ Cx.BlockGood.goodR (A.A.fam.L j A.A.μ0) (A.A.fam.lvlA F.P0 F.ψ0) ∧
      (∀ i, (A.liftI j A.A.μ0).opAll i x = s i • x) ∧ R.thG j A.A.μ0 (R.jV j A.A.μ0 x) ∈ u.2 j c ∧
      R.thG j A.A.μ0 (R.jV j A.A.μ0 x) ≠ 0) →
    ∀ k : (A.liftI j A.A.μ0).PlI × List ℕ, s (Sum.inr k) = tr j p.1.2 ((A.liftI j A.A.μ0).plI k.1, k.2)

def partAtW (F : Face3 D A) (X : Cx.CxData A.fam3.amb3) (i : Fin D.R.m) (p : A.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) : Prop :=
  ∃ x, X.tC F.cr false i A.A.μ0 (Cx.cpt A.A.v0.embedding x) ∈ X.Wp i p ∧
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((Cx.lv (F.fc X.zs) false).XT i A.A.μ0) v x x ≠ 0

end General

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) (F : Face3 a.D A)

theorem eec_eq : R.EEc = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEc) :)) :=
  (by with_unfolding_all exact ((congrArg (fun (m : type_of% (@partFull a.D)) (c : Pl a.D.host.E → List ℤ → ℂ) =>
    (m R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF fun P d => c P (dualLab d)).comap
      R.HE.e) (partFull_eq b a)) :))

theorem wc_eq : R.Wc' = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wc') :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (W : type_of% R.toRealDat.Wat) (m : type_of% (@partFull a.D)) (i : Fin a.D.R.m)
      (c : Pl a.D.host.E → List ℤ → ℂ) =>
    (W i (sg0 a.D A.A) R.triv ⊓
      m R.θ (R.MW i (sg0 a.D A.A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) R.SF c).comap
      (R.HW i _).e) (wat_eq b R.toRealDat) (partFull_eq b a)) :))

theorem carries_eq : R.Carries = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Carries) :)) :=
  (by with_unfolding_all exact ((congrArg (carriesW R) (eec_eq b R)) :))

theorem realAdelicInertTransport_typeRows_eq : R.EEp3 = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEp3) :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (Q : type_of% R.Carries) (E : type_of% R.EEc) (p : A.fam3.base3.Ix) =>
    ⨆ (c : Pl a.D.host.E → List ℤ → ℂ) (_ : Q p c), E c) (carries_eq b R) (eec_eq b R)) :))

theorem wp3_apply_eq_sq_mul_sub_sq_mul : R.Wp3 = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wp3) :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (Q : type_of% R.Carries) (E : type_of% R.Wc') (i : Fin a.D.R.m) (p : A.fam3.base3.Ix) =>
    ⨆ (c : Pl a.D.host.E → List ℤ → ℂ) (_ : Q p c), E i c) (carries_eq b R) (wc_eq b R)) :))

theorem parts_eq (_F : Face3 a.D A) : ((R.EEp3, R.toRealDat.EEat, R.Wp3) : Parts R) =
    ((by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEp3) :)), (by with_unfolding_all exact ((letI := alg b iK; (real b R.toRealDat).EEat) :)), (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wp3) :))) :=
  (by with_unfolding_all exact ((Prod.ext (realAdelicInertTransport_typeRows_eq b R) (Prod.ext (eeat_eq b R.toRealDat) (wp3_apply_eq_sq_mul_sub_sq_mul b R)) :
    ((R.EEp3, R.toRealDat.EEat, R.Wp3) : Parts R) = (_, _, _)) :))

theorem toCx3_eq : R.toCx3 F = (@RealDat3.toCx3 (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 I0 T (@famInThreeCoefficientChange B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R) (@face3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A F)) :=
  (by with_unfolding_all exact ((congrArg (cxW R F) (parts_eq b R F)) :))

theorem trISem_eq : R.TrISem F = (@RealDat3.TrISem (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 I0 T (@famInThreeCoefficientChange B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R) (@face3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A F)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun Q E => trSemW R F (Q, E)) (carries_eq b R) (wc_eq b R)) :))

variable {R F}

theorem isInert_tr (h : R.IsInert) : letI := alg b iK; (real3 b R).IsInert := by
  letI := alg b iK
  constructor
  case tie => tr_clause a b h.tie
  case onto => exact (by with_unfolding_all exact (h.onto :))
  case hR => exact (by with_unfolding_all exact (h.hR :))
  case hL => exact (by with_unfolding_all exact (h.hL :))
  case SF => exact (by with_unfolding_all exact (h.SF :))

theorem isTup_tr (h : R.IsTup) : letI := alg b iK; (real3 b R).IsTup := by
  letI := alg b iK
  constructor
  case mu_off => exact (by with_unfolding_all exact (h.mu_off :))
  case mu_used => exact (by with_unfolding_all exact (h.mu_used :))
  case mu_ne => exact (by with_unfolding_all exact (h.mu_ne :))
  case mu_conj => exact (by with_unfolding_all exact (h.mu_conj :))
  case mu_on => exact (by with_unfolding_all exact (h.mu_on :))

theorem isScal_tr (h : R.IsScal F) : letI := alg b iK; (real3 b R).IsScal (face3 b F) := by
  letI := alg b iK
  constructor
  case lam0 => tr_via (fun W : type_of% R.Wp3 => ∀ i t p (l : ℝ), W i p ≠ ⊥ →
      (∀ x ∈ W i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) → R.lam3 i t p A.A.v0 = l) (wp3_apply_eq_sq_mul_sub_sq_mul b R) h.lam0
  case kap => tr_via (fun E : type_of% R.EEp3 => ∀ κ : ℝ,
      Lift.IsKap a.D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) E R.lamN κ →
      (∃ t p, E p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 a.D.R.m, R.lamN t j p ≠ 0) → R.kap = κ) (realAdelicInertTransport_typeRows_eq b R) h.kap
  case off => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ i p v (l : ℝ), v ≠ A.A.v0 → partAtW F X i p v →
      (∀ x, X.tC F.cr false i A.A.μ0 (Cx.cpt A.A.v0.embedding x) ∈ X.Wp i p → ∀ y,
        inner ℂ (X.wC false i v (Cx.cpt v.embedding ((X.liftMat F.cr false i A.A.μ0).mulVec x)))
            (X.wC false i v (Cx.cpt v.embedding ((X.liftMat F.cr false i A.A.μ0).mulVec y))) =
          ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun a.D.what₂.LL _) ((Cx.lv (F.fc X.zs) false).XT i A.A.μ0) v x y) →
      R.lam3 i A.A.μ0 p v = l) (toCx3_eq b R F) h.off
  case abs0 => tr_via (fun u : Parts R => ∀ i t p, u.2.2 i p = ⊥ →
      R.lam3 i t p A.A.v0 = Real.exp ((F.Zsc (cxW R F u).zs).l6m i)) (parts_eq b R F) h.abs0
  case abs => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ i p v, v ≠ A.A.v0 → ¬ partAtW F X i p v →
      R.lam3 i A.A.μ0 p v = Real.exp ((F.Zsc X.zs).l6m i)) (toCx3_eq b R F) h.abs
  case tup => exact (by with_unfolding_all exact (h.tup :))

theorem primRows3_tr (h : PrimRows3 R F) : letI := alg b iK; PrimRows3 (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case heckeR => exact (by with_unfolding_all exact (h.heckeR :))
  case heckeL => exact (by with_unfolding_all exact (h.heckeL :))
  case hecke => tr_via (fun X : Cx.CxData A.fam3.amb3 => (∃ hE, Cx.HeckeIntertwiningDefinite A X hE) ∧ ∃ hW, Cx.HeckeIntertwiningLifts A X hW) (toCx3_eq b R F) h.hecke
  case gUnit => exact (by with_unfolding_all exact (h.gUnit :))
  case gEquiv => tr_via (fun u : Parts R => Cx.GEquiv3 A (cxW R F u) ((by with_unfolding_all exact ((R.gEx F) :))) ∧ Cx.LiftGroupEquivariance A (cxW R F u) ((by with_unfolding_all exact ((R.gWx F) :)))) (parts_eq b R F) h.gEquiv
  case block => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.zs.InBlock) (toCx3_eq b R F) h.block
  case rowTest => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.RowTest X) (toCx3_eq b R F) h.rowTest
  case liftTest => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTest X) (toCx3_eq b R F) h.liftTest
  case liftTestB => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTestB X false) (toCx3_eq b R F) h.liftTestB
  case liftOnto => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ hW, Cx.HeckeIntertwiningLifts A X hW →
      U2.OntoC A X F.P0 F.ψ0 F.P1 F.ψ1 hW) (toCx3_eq b R F) h.liftOnto
  case pos => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ c, (Cx.lv (F.fc X.zs) c).Pos) (toCx3_eq b R F) h.pos
  case posScal => exact (by with_unfolding_all exact (h.posScal :))
  case levE => tr_via (fun u : Parts R =>
      Cx.LevType3 A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gEx F) :))) false F.P0 F.ψ0 ∧
      Cx.LevType3 A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gEx F) :))) true F.P1 F.ψ1) (parts_eq b R F) h.levE
  case h2P => tr_via (fun X : Cx.CxData A.fam3.amb3 =>
      Cx.PrincipalLevelBijectivity A X (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) (toCx3_eq b R F) h.h2P
  case thmB => tr_via (fun E : type_of% R.EEp3 =>
      Lift.IsKap a.D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) E R.lamN R.kap) (realAdelicInertTransport_typeRows_eq b R) h.thmB
  case sumE => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ c, X.PartsE c) (toCx3_eq b R F) h.sumE
  case unif => exact (by with_unfolding_all exact (h.unif :))
  case mLat => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.MLat false) (toCx3_eq b R F) h.mLat
  case levW => tr_via (fun u : Parts R =>
      Cx.LevelTypeOfLifts A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gWx F) :))) false F.P0 F.ψ0) (parts_eq b R F) h.levW
  case thmA => tr_via (fun W : type_of% R.Wp3 => ∀ i t,
      Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (W i) fun p => R.lam3 i t p A.A.v0) (wp3_apply_eq_sq_mul_sub_sq_mul b R) h.thmA
  case sumW => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.PartsW false) (toCx3_eq b R F) h.sumW
  case scalConj => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.GalD F.cr false) (toCx3_eq b R F) h.scalConj
  case dimParts => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.DimParts false) (toCx3_eq b R F) h.dimParts

theorem realAdelicInertTransport_furtherRows (h : UnusedChoiceStatements R F) : letI := alg b iK; UnusedChoiceStatements (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case ex => exact (by with_unfolding_all exact ((exAt_tr b h.ex) :))
  case conj => exact (by with_unfolding_all exact (h.conj :))
  case levelW => exact (by with_unfolding_all exact ((lLevelW_tr b h.levelW) :))
  case integral => exact (by with_unfolding_all exact (h.integral :))

end Three

end GlobalTheory.Mem.R3.Tr

end
end

