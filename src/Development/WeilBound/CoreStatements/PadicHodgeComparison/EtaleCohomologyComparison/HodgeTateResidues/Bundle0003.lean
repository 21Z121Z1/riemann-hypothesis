import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

structure RhoEx : Prop where
  ex : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m → ∀ x : Y.Fam M r j, CB.Comp x → ∃! w, L.Rho x w
  add : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (x y : Y.Fam M r j) w w', L.Rho x w → L.Rho y w' → L.Rho (x + y) (w + w')
  smul : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (c • x) (L.ι (L.lam c) • w)

def CoEx : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m →
  Spans L.γB M.q (L.QB M) L.tB_mem r j ∧ ∃ co, IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j co

def HomRho : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n)),
  (∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u) →
  ∀ (r j : ℕ) (x : Y.Fam N r j) (w : HG (L.QB N) r j), L.Rho x w →
    L'.Rho (M := M) (fun n => (pdOm (mm n) sΛ (h.cris n) r).pull j (x n)) (h.fW u hu r j w)

def HomMu : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a r j : ℕ) (y : Hdg N.q a j),
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y)

structure MulRho : Prop where
  sh : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w)
  sh_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ), a ≤ r → ∀ y : Hdg M.q a j,
    shG (L.QB M) L.tB_mem k h j (L.μ M a r j y) = L.μ M a r' j y
  cup : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) w w',
    L.Rho x w → L.Rho y w' → L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w')
  cup_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c), a ≤ r → a' ≤ r' →
    ∀ (y : Hdg M.q a i) (y' : Hdg M.q a' j),
    cupG (L.QB M) h (L.μ M a r i y) (L.μ M a' r' j y') = L.μ M c s (i + j) (cupH M.q ha rfl y y')
  one : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q))

def FirstChernHodgeTateCompat : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), 1 < m → ∀ (D : E.LineData M.X), sSup (𝒱D D) = ⊤ →
  ∀ (x : Y.Fam M 1 2) (c : Hdg M.q 1 2), CB.IsFirstChernClassInFamily D x → IsDlogFirstChernClass M.q (genD D) c → L.Rho x (L.μ M 1 1 2 c)

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.GaloisTTransform
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dividedPowerFiltration_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 = J := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun z hz => by simpa using pow_mem_pdP δ hz 1
  rintro _ ⟨L, hL, hr, rfl⟩
  induction L with
  | nil => simp at hr
  | cons q L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hr ⊢
    rcases Nat.eq_zero_or_pos q.1 with h | h
    · exact J.mul_mem_left _ (ih (fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')) (by omega))
    · exact J.mul_mem_right _ (δ.dpow_mem h.ne' (hL q List.mem_cons_self))

structure Br (R : Per l K) (Y : CB l K) (e : Y.Λ →+* R.A) (θP : R.P →+* ℂ_[l]) (sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ)
    (sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n) (sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]) (c : K.fixingSubgroup → ℂ_[l]) : Prop where
  et : e Y.t = R.t
  t_ne : R.tB ≠ 0
  θ_i : ∀ x, ∃ y : R.P, (y : R.B) = R.i (e x) ∧ θP y = Y.θ x
  θ_o : ∀ k : K, ∃ y : R.P, (y : R.B) = R.o k ∧ θP y = kC K k
  ker : ∀ x : R.P, θP x = 0 ↔ ∃ y : R.P, (x : R.B) = R.tB * y
  θ_σ : ∀ (g : K.fixingSubgroup) (x : R.P), ∃ y : R.P, R.σ g x = y ∧ θP y = sC g (θP x)
  galois_t_transform : ∀ g : K.fixingSubgroup, ∃ u : R.P, R.σ g R.tB = u * R.tB ∧ θP u = c g
  eσ : ∀ g x, e (sΛ g x) = R.σA g (e x)
  cris : ∀ g n x, sn g n (Y.c n x) = Y.c n (sΛ g x)

variable {R : Per l K} {Y : CB l K} {e : Y.Λ →+* R.A} {θP : R.P →+* ℂ_[l]} {sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ}
  {sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n} {sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]} {c : K.fixingSubgroup → ℂ_[l]}
  (hb : Br R Y e θP sΛ sn sC c) {m : ℕ} {L : Lev R m} (hL : L.Good)

include hb hL

theorem Br.θ_ex : ∃ θ : L.B →+* ℂ_[l], ∀ x, θ (L.toB x) = θP x := by
  refine ⟨(L.toB.liftOfSurjective hL.toB_surj) ⟨θP, fun x hx => ?_⟩, fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  obtain ⟨y, hy⟩ := (hL.toB_ker x).1 hx
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  rw [hb.et] at ht
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL.pos
  refine (hb.ker x).2 ⟨t ^ k * y, ?_⟩
  rw [hy, hk, pow_add, pow_one, Subring.coe_mul, SubmonoidClass.coe_pow, ht, mul_assoc]
  rfl

theorem Br.t_ex : ∃ t : R.P, (t : R.B) = R.tB ∧ L.ι (L.lam (e Y.t)) = L.toB t ∧ L.IB = Ideal.span {L.toB t} := by
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  refine ⟨t, by rw [ht, hb.et]; rfl, hL.ι_lam _ t ht, ?_⟩
  rw [← dividedPowerFiltration_one L.γB, hL.pdP_B 1 t (by rw [ht, hb.et]; rfl), pow_one]

def Br.θ : L.B →+* ℂ_[l] := (hb.θ_ex hL).choose

theorem Br.θ_toB (x : R.P) : hb.θ hL (L.toB x) = θP x := (hb.θ_ex hL).choose_spec x

theorem Br.ker_θ : RingHom.ker (hb.θ hL) = L.IB := by
  obtain ⟨t, ht, -, hI⟩ := hb.t_ex hL
  ext b
  obtain ⟨x, rfl⟩ := hL.toB_surj b
  rw [RingHom.mem_ker, hb.θ_toB, hI, Ideal.mem_span_singleton']
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (hb.ker x).1 h
    refine ⟨L.toB y, ?_⟩
    rw [← map_mul]
    exact congrArg L.toB (Subtype.ext (by rw [hy, Subring.coe_mul, ht, mul_comm]))
  · rintro ⟨a, ha⟩
    have h0 : θP t = 0 := (hb.ker t).2 ⟨1, by rw [ht]; simp⟩
    rw [← hb.θ_toB hL, ← ha, map_mul, hb.θ_toB, h0, mul_zero]

theorem Br.gr (i : ℕ) (hi : i < m) (x : L.B)
    (h : x * L.ι (L.lam (e Y.t)) ^ i ∈ Ideal.span {L.ι (L.lam (e Y.t)) ^ (i + 1)}) : x ∈ L.IB := by
  obtain ⟨t, ht, h1, hI⟩ := hb.t_ex hL
  rw [h1] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨x, rfl⟩ := hL.toB_surj x
  obtain ⟨a, rfl⟩ := hL.toB_surj a
  have h2 : L.toB (x * t ^ i - a * t ^ (i + 1)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, ha, sub_self]
  obtain ⟨y, hy⟩ := (hL.toB_ker _).1 h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have h3 : x = (a + t ^ k * y) * t := by
    refine Subtype.ext (mul_right_cancel₀ (pow_ne_zero i hb.t_ne) ?_)
    push_cast at hy ⊢
    rw [ht] at hy ⊢
    linear_combination hy
  rw [hI, h3, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def Br.lv (hd : ∀ n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) L.γ l n, ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ (L.lam (e x))) :
    Lv Y m where
  B := L.B
  IB := L.IB
  γB := L.γB
  θ := hb.θ hL
  A := L.A
  I := L.I
  γ := L.γ
  ι := L.ι
  lam := L.lam.comp e
  d n := (hd n).choose
  d_lam n := (hd n).choose_spec
  lat := hL.lat m le_rfl
  ι_dp := hL.ι_dp
  ι_O := hL.ι_O
  t_mem := by
    obtain ⟨t, -, h1, hI⟩ := hb.t_ex hL
    rw [hL.ι_I, Ideal.mem_comap, RingHom.comp_apply, h1, hI]
    exact Ideal.mem_span_singleton_self _
  θ_K k := by
    obtain ⟨y, h1, h2⟩ := hb.θ_o k
    rw [← hL.toB_K k y h1, hb.θ_toB, h2]
  θ_lam x := by
    obtain ⟨y, h1, h2⟩ := hb.θ_i x
    rw [RingHom.comp_apply, hL.ι_lam _ y h1, hb.θ_toB, h2]
  ker_θ := hb.ker_θ hL
  pdB r := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, hL.pdP_B r t ht]
  nil := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, ← map_pow]
    exact (hL.toB_ker _).2 ⟨1, by simp [ht]⟩
  gr := hb.gr hL

theorem Br.gal (hd) (g : K.fixingSubgroup) : Nonempty (LHom (hb.lv hL hd) (hb.lv hL hd) (sΛ g) (sn g) (sC g) (c g)) := by
  obtain ⟨u, hu, hc⟩ := hb.galois_t_transform g
  obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
  exact ⟨{
    le := le_rfl
    sA := L.σA g
    sB := L.σB g
    dpA := hL.σ_dp g
    dpB := hL.σB_dp g
    oA := hL.σ_O g
    oB := hL.σB_K g
    ι := fun a => (hL.σ_ι g a).symm
    lam := fun x => (hL.σ_lam g (e x)).trans (congrArg L.lam (hb.eσ g x).symm)
    cris := hb.cris g
    θ := fun b => by
      obtain ⟨x, rfl⟩ := hL.toB_surj b
      obtain ⟨y, h2, h3⟩ := hb.θ_σ g x
      change hb.θ hL (L.σB g (L.toB x)) = sC g (hb.θ hL (L.toB x))
      rw [hL.σB_toB g x y h2, hb.θ_toB, hb.θ_toB, h3]
    cB := L.toB u
    t := by
      change L.σB g (L.ι (L.lam (e Y.t))) = L.toB u * L.ι (L.lam (e Y.t))
      rw [h1, ← map_mul]
      exact hL.σB_toB g t (u * t) (by rw [Subring.coe_mul, ht, hu])
    θc := (hb.θ_toB hL u).trans hc }⟩

omit hL in
theorem Br.sys (S : LevSys R) (hS : S.Good)
    (hd : ∀ m n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) (S.L m).γ l n,
      ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ ((S.L m).lam (e x))) : Nonempty (LvSys Y sΛ sn sC c) :=
  ⟨{ L := fun m => hb.lv (hS.lev m) (hd m)
     dn := fun m =>
      { le := Nat.le_succ _
        sA := S.dA m
        sB := S.dB m
        dpA := hS.ddp m
        dpB := hS.ddpB m
        oA := hS.dO m
        oB := hS.dK m
        ι := hS.dι m
        lam := fun x => hS.dlam m (e x)
        cris := fun _ _ => rfl
        θ := fun b => by
          obtain ⟨x, rfl⟩ := (hS.lev (m + 1)).toB_surj b
          change hb.θ (hS.lev m) (S.dB m ((S.L (m + 1)).toB x)) = hb.θ (hS.lev (m + 1)) ((S.L (m + 1)).toB x)
          rw [hS.dB_toB, hb.θ_toB, hb.θ_toB]
        cB := 1
        t := by
          change S.dB m ((S.L (m + 1)).ι ((S.L (m + 1)).lam (e Y.t))) = 1 * (S.L m).ι ((S.L m).lam (e Y.t))
          rw [hS.dι, hS.dlam, one_mul]
        θc := map_one _ }
     gal := fun m g => (hb.gal (hS.lev m) (hd m) g).some }⟩

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.MulSubMulTo
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

theorem sub_mulTo (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F') (h) (c : R) (hc) (c' a : R') (hc') (e : σ c = a * c')
    (j : ℕ) (y : CH.H F j) :
    (subMor m S S' h).pull j ((mulTo c S hc).pull j y) = a • (mulTo c' S' hc').pull j (m.pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • z.1 (s ⋙ m.G)) = a • c' • m.τ _ (z.1 (s ⋙ m.G))
  rw [LinearMap.map_smulₛₗ, e, mul_smul]

theorem sub_mulSub (m : CH.Mor F F' σ) (S₁ S₂ : CH.SubF F) (S₁' S₂' : CH.SubF F') (h₁ h₂) (c : R) (hc) (c' : R') (hc') (e : σ c = c')
    (j : ℕ) (y : CH.H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ hc).pull j y) = (mulSub c' S₁' S₂' hc').pull j ((subMor m S₁ S₁' h₁).pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • (show S₁.S _ from z.1 (s ⋙ m.G)).1) = c' • m.τ _ (show S₁.S _ from z.1 (s ⋙ m.G)).1
  rw [LinearMap.map_smulₛₗ, e]

theorem mulSub_mulTo (S S' : CH.SubF F) (c c' c'' : R) (h h' h'') (e : c' * c = c'') (j : ℕ) (y : CH.H F j) :
    (mulSub c' S S' h').pull j ((mulTo c S h).pull j y) = (mulTo c'' S' h'').pull j y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change c' • c • z.1 s = c'' • z.1 s
  rw [smul_smul, e]

theorem sub_square {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R} {F₂ : C₂ ⥤ ModuleCat.{0} R} {F₃ : C₃ ⥤ ModuleCat.{0} R} {F₄ : C₄ ⥤ ModuleCat.{0} R}
    {σ₁ σ₂ σ₃ σ₄ : R →+* R} (τ : R →+* R) [RingHomCompTriple σ₁ σ₂ τ] [RingHomCompTriple σ₃ σ₄ τ]
    (m : CH.Mor F₁ F₂ σ₁) (b : CH.Mor F₂ F₃ σ₂) (b' : CH.Mor F₁ F₄ σ₃) (q : CH.Mor F₄ F₃ σ₄)
    (S₁ : CH.SubF F₁) (S₂ : CH.SubF F₂) (S₃ : CH.SubF F₃) (S₄ : CH.SubF F₄) (hm hb hb' hq)
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x)) (n : ℕ) (x : CH.H S₁.fn n) :
    (subMor b S₂ S₃ hb).pull n ((subMor m S₁ S₂ hm).pull n x) = (subMor q S₄ S₃ hq).pull n ((subMor b' S₁ S₄ hb').pull n x) := by
  rw [pull_pull τ, pull_pull τ]
  exact CrystallineSemistableComparison.P.prism ((subMor m S₁ S₂ hm).comp (σ'' := τ) (subMor b S₂ S₃ hb))
    ((subMor b' S₁ S₄ hb').comp (σ'' := τ) (subMor q S₄ S₃ hq)) η (fun T x => Subtype.ext (hτ T x.1)) n x

end Gen

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section P
variable (ht : TFil l) (P : PAlg l ⥤ Type)

def shT {r r' : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) : CH.Mor (TT P r n).fn (TT P r' n).fn (RingHom.id _) :=
  mulSub (tA l ^ k) (TT P r n) (TT P r' n) fun T (x : T.1.obj.Acr n) hx => mem_TT.2 (by
    have := dividedPowerFiltration_pow_mul (B.DD false T.1.obj n) (ht T.1.obj n) h (mem_TT.1 hx)
    rw [← map_pow] at this
    exact this)

theorem shT_tMor {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ) (y : MH P n j) :
    (shT ht P k h n).pull j ((tMor ht P r n).pull j y) = (tMor ht P r' n).pull j y :=
  mulSub_mulTo (TT P r n) (TT P r' n) (tA l ^ r) (tA l ^ k) (tA l ^ r') _ _ _ (by rw [← pow_add, add_comm, h]) j y

variable {P}

def galT (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n : ℕ) : CH.Mor (TT P r n).fn (TT P r n).fn (ACris.galCris σ) :=
  subMor (galMor σ a n) (TT P r n) (TT P r n) fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (GlobalTheory.CompanionTheory.BetaGal.dd_twAcr false σ T.1.obj n) r ((mem_TT (T := (elTw σ a).obj T)).1 hx))

theorem galT_tMor (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n j : ℕ) (y : MH P n j) :
    (galT σ a r n).pull j ((tMor ht P r n).pull j y) = χA σ ^ r • (tMor ht P r n).pull j ((galMor σ a n).pull j y) :=
  sub_mulTo (galMor σ a n) (TT P r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) (χA σ ^ r) _
    (by rw [map_pow, galCris_tA, mul_pow]) j y

def pullT' {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n : ℕ) : CH.Mor (TT P' r n).fn (TT P r n).fn (RingHom.id _) :=
  subMor (pullMor u n) (TT P' r n) (TT P r n) fun T x hx => mem_TT.2 ((mem_TT (T := (elMap u).obj T)).1 hx)

theorem pullT_tMor {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n j : ℕ) (y : MH P' n j) :
    (pullT' u r n).pull j ((tMor ht P' r n).pull j y) = (tMor ht P r n).pull j ((pullMor u n).pull j y) :=
  (sub_mulTo (pullMor u n) (TT P' r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) 1 _ (one_mul _).symm j y).trans (one_smul _ _)

end P

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r' n).pull j ((pdSh (B.Lc F κ false n) ((base l).cris n) (ht (base l) n) k h).pull j x) =
      (shT ht (F.pt κ) k h n).pull j ((βMorF F κ r n).pull j x) :=
  sub_mulSub (B.βMor F κ false n) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r')
    (TT (F.pt κ) r n) (TT (F.pt κ) r' n) _ _ (tA l ^ k) _ (tA l ^ k) _ rfl j x

theorem β_galF (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j x) =
      (galT σ (B.ptTw F κ σ hσ) r n).pull j ((βMorF F κ r n).pull j x) := by
  have h1 := pull_pull (ACris.galCris σ) (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r)
    (βMorF F κ r n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMorF F κ r n) (galT σ (B.ptTw F κ σ hσ) r n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (pd_pull_eq ((βMorF F κ r n).comp (σ'' := ACris.galCris σ) (galT σ (B.ptTw F κ σ hσ) r n))
    ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).comp (σ'' := ACris.galCris σ) (βMorF F κ r n))
    (GlobalTheory.CompanionTheory.BetaGal.etaGal F κ σ hσ false n) (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ _ _ => rfl) j x).symm

variable {F} {F' : B.Fn O}

theorem β_pullF (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pullT' (u.pt κ) r n).pull j ((βMorF F' κ r n).pull j x) :=
  sub_square (RingHom.id _) (B.pullMorC κ u false n) (B.βMor F κ false n) (B.βMor F' κ false n) (pullMor (u.pt κ) n)
    (B.pdS (B.Lc F' κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (TT (F.pt κ) r n) (TT (F'.pt κ) r n)
    _ _ _ _ (GlobalTheory.CompanionTheory.BetaPull.cmpNat κ u false n) (fun _ _ => rfl) j x

end F

end CrystallineSemistableComparison.HT
end
end

