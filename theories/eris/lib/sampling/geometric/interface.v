From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import utils. 

Class geometric_spec `{!erisGS Σ} (geometric_prog geometric_alloc : val) :=
  GeometricSpec
  {
    twp_geometric_adv_comp :
    ∀ (p q : nat),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      ∀ (D : nat → R) (L : R) (ε : R),
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, ((p / (q + 1)) * (1 - p / (q + 1))^k * D k)%R) = ε →
      ↯ ε -∗ WP geometric_prog #() #p #q [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }];

    own_geometric_tape (α : loc) (N M : nat) (v : list nat) : iProp Σ;

    twp_geometric_alloc (p q : nat) :
      [[{ True }]]
        geometric_alloc #p #q
      [[{ (α : loc), RET #lbl:α; own_geometric_tape α p q [] }]];
    
    twp_geometric_tape :
    ∀ (p q r : nat) (α : loc) (n : nat) (ns : list nat) (Φ : val → iProp Σ),
      own_geometric_tape α p q (n::ns) -∗
      (own_geometric_tape α p q ns -∗ Φ #n) -∗
      WP geometric_prog #lbl:α #p #q #r [{ Φ }];
 
    twp_geometric_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q r : nat) (ns : list nat) (ε : R),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      to_val e = None →
      own_geometric_tape α p q ns ∗
      (∀ (i : nat), own_geometric_tape α p q (ns ++ [i]) -∗ WP e [{ Φ }])
      ⊢  WP e [{ Φ }];
  
    twp_geometric_planner :
    ∀ (p q r : nat) (α : loc) (e : expr)
      (L_size L_sum : nat) (Φ : val → iProp Σ)
      (prefix : list nat) (suffix : list nat → list nat) ,
      (0 < p < q + 1)%nat →
      0 < r →
      to_val e = None →
      (∀ (junk : list nat),
         0 < length (suffix (prefix ++ junk)) <= L_size ∧ list_sum (suffix (prefix ++ junk)) ≤ L_sum) →
      own_geometric_tape α p q prefix ∗
      ((∃ (junk : list nat),
           own_geometric_tape α p q (prefix ++ junk ++ suffix (prefix ++ junk)))
       -∗ WP e [{ Φ }])
      ⊢ WP e [{ Φ }];

    twp_geometric_presample_adv_comp :
    ∀ (p q : nat) (α : loc) (l : list nat) (e : expr) (Φ : val → iProp Σ),
      0 < p →
      p ≤ (q + 1) →
      to_val e = None →
      ∀ (r : nat) (D : nat → R) (L : R) (ε : R),
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, ((p / (q + 1)) * (1 - p / (q + 1))^k * D k)%R) = ε →
      ↯ ε ∗
      own_geometric_tape α p q l ∗
      (∀ (n : nat),
         ↯ (D n) -∗
         own_geometric_tape α p q (l ++ [n]) -∗ WP e [{ Φ }]) ⊢
      WP e [{ Φ }]
  }.
