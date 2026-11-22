import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowers
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpAdjoint

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

theorem iso_up {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) : LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN'
    (H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull N h h rfl)) b.symm)

end Bundles

section Field

variable {K : Type} [Field K] {S' : Scheme.{0}} (f : S' ⟶ Sp K)

theorem exists_point [Nonempty S'] :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (x : Sp K' ⟶ S'), x ≫ f = spMap i := by
  obtain ⟨y⟩ := ‹Nonempty S'›
  obtain ⟨i, hi⟩ := Spec.map_surjective (S'.fromSpecResidueField y ≫ f)
  exact ⟨S'.residueField y, inferInstance, i.hom, S'.fromSpecResidueField y, hi.symm⟩

variable {f}

theorem iso_down [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) (h₁ : Smooth p₀) (h₂ : IsProper p₀) (h₃ : GeometricallyConnected p₀)
    {M N : LB X₀} {M' N' : LB X} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (c : LBIso M' N') : LBIso M N := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have P : IsPullback (pullback.fst p x ≫ h) (pullback.snd p x) p₀ (spMap i) :=
    hx ▸ (IsPullback.of_hasPullback p x).paste_horiz H
  have d : LBIso (M.pull h) (N.pull h) := LBIso.trans (pull_isLB hM h) hM' (pull_isLB hN h) a.symm
    (LBIso.trans hM' hN' (pull_isLB hN h) c b)
  exact (GlobalTheory.lb_gen_iso_descend_field K K' i X₀ _ p₀ _ _ h₁ h₂ h₃ P).2 M N hM hN (d.chartPull
    (chartPullSame M _ _ _ (pullback.fst p x) fun _ => rfl) (chartPullSame N _ _ _ (pullback.fst p x) fun _ => rfl))

end Field

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

theorem iso_cubeLB_pull [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}
    (H : LBIso L' (L.pull φ)) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : pushPt h.1.w a' = U ≫ a)
    (hb : pushPt h.1.w b' = U ≫ b) : LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) :=
  iso_linComb_pull H _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

end Points

def sqMap : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem push_fst : pushPt h.1.w (fst G' G') = sqMap h ≫ fst G G := (lift_fst _ _).symm

theorem push_snd : pushPt h.1.w (snd G' G') = sqMap h ≫ snd G G := (lift_snd _ _).symm

theorem isPullback_sqMap : IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ := congrArg (fun q => q.left) (push_fst h).symm
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ := congrArg (fun q => q.left) (push_snd h).symm
  have A : IsPullback (snd G G).left (fst G G).left G.hom G.hom := (IsPullback.of_hasPullback G.hom G.hom).flip
  have A' : IsPullback (snd G' G').left (fst G' G').left G'.hom G'.hom := (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have B := A'.paste_horiz h.1
  rw [← e₂, ← h.1.w] at B
  have C := (IsPullback.of_right B e₁ A).paste_vert h.1
  rwa [Over.w, Over.w] at C

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a :=
  Over.OverMorphism.ext ha

end Group

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

theorem isLB_linComb {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _

theorem transfer {K : Type} [Field K] {S₁ S₂ : Scheme.{0}} [Nonempty S₁] {s₀ : Sp K ⟶ Sp o} {s₁ : S₁ ⟶ Sp o}
    {s₂ : S₂ ⟶ Sp o} {f₁ : S₁ ⟶ Sp K} {f₂ : S₂ ⟶ Sp K} {t₀ : TObj g k J b s₀} {t₁ : TObj g k J b s₁}
    {t₂ : TObj g k J b s₂} (H₁ : TMap t₁ t₀ f₁) (H₂ : TMap t₂ t₀ f₂) (w w' : J) :
    (LBIso (cubeLB t₁.A ![fst t₁.A t₁.A ≫ t₁.act w, snd t₁.A t₁.A] t₁.L)
        (cubeLB t₁.A ![fst t₁.A t₁.A, snd t₁.A t₁.A ≫ t₁.act w'] t₁.L) →
      LBIso (cubeLB t₂.A ![fst t₂.A t₂.A ≫ t₂.act w, snd t₂.A t₂.A] t₂.L)
        (cubeLB t₂.A ![fst t₂.A t₂.A, snd t₂.A t₂.A ≫ t₂.act w'] t₂.L)) ∧
    (LBIso t₁.L (cubeLB t₁.A ![𝟙 t₁.A, t₁.act w] t₁.L) → LBIso t₂.L (cubeLB t₂.A ![𝟙 t₂.A, t₂.act w] t₂.L)) := by
  obtain ⟨φ, h, hL, -, hact⟩ := H₁
  obtain ⟨φ', h', hL', -, hact'⟩ := H₂
  let _ := t₀.ab.comm
  let _ := t₁.ab.comm
  let _ := t₂.ab.comm
  have := t₀.ab.smooth
  have := t₀.ab.proper
  have := t₀.ab.geomConnected
  have pr : IsProper (t₀.A ⊗ t₀.A).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have i₂ := iso_cubeLB_pull h _ hL (push_comp h _ (push_fst h) (hact w)) (push_snd h)
  have i₃ := iso_cubeLB_pull h _ hL (push_fst h) (push_comp h _ (push_snd h) (hact w'))
  have i₄ := iso_cubeLB_pull h _ hL (push_id h) (push_end h (hact w))
  have j₂ := iso_cubeLB_pull h' _ hL' (push_comp h' _ (push_fst h') (hact' w)) (push_snd h')
  have j₃ := iso_cubeLB_pull h' _ hL' (push_fst h') (push_comp h' _ (push_snd h') (hact' w'))
  have j₄ := iso_cubeLB_pull h' _ hL' (push_id h') (push_end h' (hact' w))
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have d := iso_down (isPullback_sqMap h) (smooth_tensorObj_hom _ _) pr (geometricallyConnected_tensorObj_hom _ _)
      (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₁.isLB _ _) (isLB_linComb t₁.isLB _ _)
      i₂ i₃ H
    exact iso_up (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₂.isLB _ _)
      (isLB_linComb t₂.isLB _ _) j₂ j₃ d
  · have d := iso_down h.1 ‹_› ‹_› ‹_› t₀.isLB (isLB_linComb t₀.isLB _ _) t₁.isLB (isLB_linComb t₁.isLB _ _) hL i₄ H
    exact iso_up t₀.isLB (isLB_linComb t₀.isLB _ _) t₂.isLB (isLB_linComb t₂.isLB _ _) hL' j₄ d

theorem adjoint_primitive_of_dense : Out.GlobalFnsSt → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j', (a j).transpose * (W + W.transpose) = (W + W.transpose) * a j' → LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act j, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act j'] t.L)) ∧ ∀ j, (W + W.transpose) * a j = W → LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act j] t.L) := by
  intro hG cube h g W J a bas k o _ b em S _ s t hd
  let _ := t.ab.comm
  have : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  refine ⟨fun j j' hj => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hG S t.A t.L _ _ t.ab t.isLB t.ample (t.hom j) (t.hom j') (hd.mono ?_),
    fun j hj => GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hG S t.A t.L _ t.ab t.isLB t.ample t.rigid (t.hom j) (hd.mono ?_)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, tx.act j', hp, hφ, tx.isLB, hL,
      hact j, hact j', (transfer m₁ m₂ j j').1 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).2 (a j') (tc.act j') (hmat j') hj)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, hp, hφ, tx.isLB, hL,
      hact j, (transfer m₁ m₂ j j).2 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).1 hj)⟩

end GlobalTheory.SharpAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SpreadLevel

theorem pushHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) :=
  ⟨fun x y hxy =>
      Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y])),
    fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem map_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S} {T' : Over S'}
    (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (y : Fin n → (T' ⟶ G')) (a : Fin n → ℕ) :
    ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  simp only [Out.linComb, map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem unitS_comp {o : Type} [CommRing o] {S S' : Scheme.{0}} (f : S' ⟶ S) (s : S ⟶ Sp o) (u : oˣ) :
    unitS (f ≫ s) u = Units.map f.appTop.hom.toMonoidHom (unitS s u) := by
  apply Units.ext
  show (f ≫ s).appTop.hom _ = f.appTop.hom (s.appTop.hom _)
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem unitS_spMap_pow {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (k : ℕ) (h : β u ^ k = 1) :
    unitS (spMap β) u ^ k = 1 := by
  apply Units.ext
  have e : (spMap β).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (β u) :=
    (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  rw [Units.val_pow_eq_pow_val]
  show (spMap β).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u) ^ k = 1
  rw [e, ← map_pow, h, map_one]

theorem exists_extension (hL : Out.Laws) {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
    {K : Type} [Field K] {S : Scheme.{0}} [PreconnectedSpace S] (s : S ⟶ Sp o) (j : Sp K ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {sK : Sp K ⟶ Sp o} (hs : j ≫ s = sK) (hk : 0 < k)
    (hζ : unitS s b.ζ ^ k = 1) (t : TObj g k J b sK)
    (P : Out.PolAV S) (φ : t.A.left ⟶ P.A.left) (hg : P.g = g) (hφ : IsGrpPullback t.A P.A j φ)
    (hφL : LBIso t.L (P.L.pull φ)) (p : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (hp : ∀ i, (t.pt i).left ≫ φ = j ≫ (p i).left) (a : J → (P.A ⟶ P.A))
    (ha : ∀ i, (t.act i).left ≫ φ = φ ≫ (a i).left) : ∃ t' : TObj g k J b s, TMap t t' j := by
  subst hs
  have := P.isAb.proper
  have := P.isAb.smooth
  have := P.isAb.comm
  have hku : IsUnit (k : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rwa [map_natCast] at this
  let h : Over.mk ((Out.baseOver (Sp K)).hom ≫ j) ⟶ Out.baseOver S := Over.homMk j (by simp)
  have hpush : ∀ i, pushHom hφ _ (t.pt i) = h ≫ p i := fun i => Over.OverMorphism.ext (hp i)
  have tors : ∀ i, p i ^ k = 1 := fun i => by
    have e : h ≫ (p i ^ k) = h ≫ (1 : Out.baseOver S ⟶ P.A) := by
      have e₁ := map_pow (preHom (G := P.A) h) (p i) k
      have e₂ := map_one (preHom (G := P.A) h)
      refine e₁.trans (Eq.trans ?_ e₂.symm)
      show (h ≫ p i) ^ k = 1
      rw [← hpush, ← map_pow, t.torsion, map_one]
    exact Over.OverMorphism.ext (ExtUnique.hom_ext_of_dominant P.A.hom (by rw [Over.w, Over.w]) j
      (congrArg CommaMorphism.left e))
  refine ⟨{ A := P.A, ab := P.isAb, dim := hg ▸ P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
            ample := P.ample, ktriv := P.ktriv, pt := p, torsion := tors, bij := ?_, pairing := fun i i' => ?_
            act := a, hom := fun i => ?_ }, φ, hφ, hφL, hp, ha⟩
  · refine GlobalTheory.torsion_basis_of_dense S P.A k (2 * g) p (Set.range j) P.isAb hk hku tors j.denseRange ?_
    rintro _ ⟨z, rfl⟩
    let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K _)
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    refine ⟨AlgebraicClosure K, inferInstance, inferInstance, x₀ ≫ j,
      ⟨IsLocalRing.closedPoint _, (Scheme.Hom.comp_apply _ _ _).trans (congrArg j (Subsingleton.elim _ _))⟩,
      fun y hy => ?_⟩
    have hb := pushHom_bijective hφ (Over.mk x₀)
    obtain ⟨y', rfl⟩ := hb.2 y
    have hy' : y' ^ k = 1 := hb.1 (by rw [map_pow, map_one]; exact hy)
    refine (existsUnique_congr fun c => ?_).1 (t.bij _ x₀ y' hy')
    rw [← hb.1.eq_iff, map_linComb]
    refine Eq.congr_left (congrArg (fun q => Out.linComb q _) (funext fun i => Over.OverMorphism.ext ?_))
    show (x₀ ≫ (t.pt i).left) ≫ φ = (x₀ ≫ j) ≫ (p i).left
    rw [Category.assoc, hp, Category.assoc]
  · obtain ⟨U, hU, H⟩ := GlobalTheory.exists_clopen_weilIs_iff hL S P k (Out.baseOver S) (p i) (p i')
      (unitS s b.ζ ^ Out.stdSymp g i i') hk hku (tors i) (tors i')
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow])
    have w := (GlobalTheory.weilIs_grpPullback_of_comm S (Sp K) P.A t.A j φ P.L t.L P.isLB t.isLB hφ hφL (Out.baseOver (Sp K))
      k (t.pt i) (t.pt i') (h ≫ p i) (h ≫ p i') _ (hp i).symm (hp i').symm).1 (t.pairing i i')
    rw [unitS_comp, ← map_zpow] at w
    have hr : Set.range h.left ⊆ U := (H _ h).1 w
    have hall : (U : Set (Out.baseOver S).left) = Set.univ :=
      IsClopen.eq_univ (α := S) ⟨hU, U.isOpen⟩ ⟨_, hr ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have := (H _ (𝟙 _)).2 (fun y _ => hall ▸ Set.mem_univ y)
    simpa using this
  · have := t.hom i
    exact ExtUnique.isMonHom_of_isGrpPullback hφ hφ (t.act i) (a i) (ha i)

theorem main : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (t : TObj g k J b (spMap (algebraMap R K) ≫ spMap β)) (P' : Out.PolAV (Sp R)) (φ : t.A.left ⟶ P'.A.left), P'.g = g → IsGrpPullback t.A P'.A (spMap (algebraMap R K)) φ → LBIso t.L (P'.L.pull φ) → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g k J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) := by
  intro hL _ o _ g k J b _ R K _ _ _ _ _ _ β t P' φ hg hφ hφL
  have := P'.isAb.proper
  have := P'.isAb.smooth
  let e : pullback P'.A.hom (spMap (algebraMap R K)) ⟶ t.A.left :=
    hφ.1.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ φ = pullback.fst _ _ := hφ.1.lift_fst _ _ _
  have e₂ : e ≫ t.A.hom = pullback.snd _ _ := hφ.1.lift_snd _ _ _
  let e' : t.A.left ⟶ pullback P'.A.hom (spMap (algebraMap R K)) := pullback.lift φ t.A.hom hφ.1.w
  have ee : e' ≫ e = 𝟙 _ := by
    apply hφ.1.hom_ext
    · rw [Category.assoc, e₁, Category.id_comp]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, e₂, Category.id_comp]; exact pullback.lift_snd _ _ _
  have wpt : ∀ i, (t.pt i).left ≫ t.A.hom = 𝟙 (Sp K) := fun i => Over.w (t.pt i)
  let v : Fin (2 * g) ⊕ J → (t.A.left ⟶ t.A.left) :=
    Sum.elim (fun i => t.A.hom ≫ (t.pt i).left) (fun j => (t.act j).left)
  have hv : ∀ i, v i ≫ t.A.hom = t.A.hom := by
    rintro (i | j)
    · exact (Category.assoc _ _ _).trans ((congrArg (t.A.hom ≫ ·) (wpt i)).trans (Category.comp_id _))
    · exact Over.w (t.act j)
  obtain ⟨f, hf, u', hu'⟩ := GlobalTheory.morphisms_generic_spread_out R K P'.A.left P'.A.left P'.A.hom P'.A.hom (Fin (2 * g) ⊕ J)
    (fun i => e ≫ v i ≫ φ) inferInstance inferInstance inferInstance (fun i => by
      rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (v i), hv, ← Category.assoc, e₂,
        pullback.condition])
  have hfK : IsUnit (algebraMap R K f) :=
    IsUnit.mk0 _ fun h0 => hf (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  let ψ : Localization.Away f →+* K := IsLocalization.Away.lift f hfK
  have hψ : ψ.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f hfK
  have hψs : spMap ψ ≫ spMap (algebraMap R (Localization.Away f)) = spMap (algebraMap R K) := by
    rw [← hψ]; exact (Spec.map_comp _ _).symm
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, m⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) x
    have h₁ := congrArg ψ h
    rw [map_mul, hx, zero_mul, ← RingHom.comp_apply, hψ] at h₁
    have h₂ : r = 0 := IsFractionRing.injective R K (h₁.symm.trans (map_zero _).symm)
    rw [h₂, map_zero] at h
    exact (IsLocalization.map_units (Localization.Away f) m).mul_left_eq_zero.1 h
  have : IsSchemeTheoreticallyDominant (spMap ψ) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hψi
  have : PreconnectedSpace (Sp (Localization.Away f)) :=
    inferInstanceAs (PreconnectedSpace (PrimeSpectrum (Localization.Away f)))
  have hprim := b.prim K ((algebraMap R K).comp β)
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by
    have := b.unit.map β
    rw [h0, Nat.cast_zero, map_zero] at this
    exact not_isUnit_zero this
  have hζ : unitS (spMap (algebraMap R (Localization.Away f)) ≫ spMap β) b.ζ ^ k = 1 := by
    rw [unitS_comp, ← map_pow, unitS_spMap_pow β b.ζ k (IsFractionRing.injective R K (by
      rw [map_pow, map_one]; exact hprim.pow_eq_one)), map_one]
  obtain ⟨P, χ, hχ₀, hgP, hm, c, hc⟩ := hL.polBaseChange _ _ (spMap (algebraMap R (Localization.Away f))) P'
  have hχ : IsGrpPullback P.A P'.A (spMap (algebraMap R (Localization.Away f))) χ :=
    ⟨hχ₀, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hχ₀.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hχ₀.w y),
        ← hm]
      rfl⟩
  let w : t.A.left ⟶ P.A.left := hχ₀.lift φ (t.A.hom ≫ spMap ψ) (by rw [Category.assoc, hψs, hφ.1.w])
  have w₁ : w ≫ χ = φ := hχ₀.lift_fst _ _ _
  have w₂ : w ≫ P.A.hom = t.A.hom ≫ spMap ψ := hχ₀.lift_snd _ _ _
  have hw : IsGrpPullback t.A P.A (spMap ψ) w := hχ.cancel (hφ.congr hψs.symm w₁.symm) w₂
  have hwL : LBIso t.L (P.L.pull w) :=
    hφL.trans t.isLB (pull_isLB P'.isLB _) (pull_isLB P.isLB _)
      (LBIso.chartPull (chartPullSame P'.L (fun _ : PUnit => φ) (fun _ : PUnit => χ) (fun _ => 1) w fun _ => w₁.symm)
        (chartPullPull P.L w w rfl) ⟨c, hc⟩)
  let d : P.A.left ⟶ pullback P'.A.hom (spMap (algebraMap R (Localization.Away f))) := pullback.lift χ P.A.hom hχ₀.w
  have d₁ : d ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  let v' : Fin (2 * g) ⊕ J → (P.A ⟶ P.A) := fun i => Over.homMk (hχ₀.lift (d ≫ u' i) P.A.hom (by
    rw [Category.assoc, (hu' i).1, ← Category.assoc, d₁, hχ₀.w])) (hχ₀.lift_snd _ _ _)
  have hv' : ∀ i, v i ≫ w = w ≫ (v' i).left := fun i => by
    have a₁ : (v' i).left ≫ χ = d ≫ u' i := hχ₀.lift_fst _ _ _
    have a₂ := (hu' i).2 (e ≫ w ≫ d) (by rw [Category.assoc, Category.assoc, d₁, w₁, e₁])
    apply hχ₀.hom_ext
    · rw [Category.assoc, Category.assoc, w₁, a₁]
      have a₃ := congrArg (e' ≫ ·) a₂
      simp only [← Category.assoc, ee, Category.id_comp] at a₃
      rw [← a₃, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w (v' i), w₂, ← Category.assoc, hv]
  have z₁ : eSec P.A ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have z₂ : eSec t.A ≫ t.A.hom = 𝟙 _ := Over.w η[t.A]
  refine ⟨f, hf, ?_⟩
  obtain ⟨t', ht'⟩ := exists_extension hL (spMap (algebraMap R (Localization.Away f)) ≫ spMap β) (spMap ψ)
    (by rw [← Category.assoc, hψs]) hk hζ t P w (hgP.trans hg) hw hwL
    (fun i => Over.homMk (eSec P.A ≫ (v' (.inl i)).left) (by
      show (eSec P.A ≫ (v' (.inl i)).left) ≫ P.A.hom = 𝟙 _
      rw [Category.assoc, Over.w (v' _), z₁]))
    (fun i => by
      show (t.pt i).left ≫ w = spMap ψ ≫ eSec P.A ≫ (v' (.inl i)).left
      refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
      refine (congrArg (· ≫ (v' (.inl i)).left) (PolBaseChange.eSec_comm hw).symm).trans ?_
      refine (Category.assoc _ _ _).trans ((congrArg (eSec t.A ≫ ·) (hv' (.inl i)).symm).trans ?_)
      show eSec t.A ≫ (t.A.hom ≫ (t.pt i).left) ≫ w = _
      rw [Category.assoc, ← Category.assoc, z₂]
      exact Category.id_comp _)
    (fun j => v' (.inr j)) (fun j => hv' (.inr j))
  exact ⟨t', ψ, hψ, ht'⟩

end GlobalTheory.SpreadLevel
end

