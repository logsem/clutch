
                
let rec power_two_decomp n =
        if n mod 2 == 1 then (n, 0)
        else let (u, t) = power_two_decomp (n/2) in (u, t+1)

                
let rec fast_mod_exp b e m =
        if e == 0 then 1
        else
                let r = fast_mod_exp ((b*b) mod m) (e/2) m in
                if e mod 2 == 0 then r
                else (b*r) mod m

                        
let rec mr_round n t u =
        let x = 1 + Random.int(n-1) in
        let y = fast_mod_exp x u n in
        if y == 1 then true
        else
                let rec aux y m k =
                        (if k == 0 then false
                        else
                                if y == m-1 then true
                                else aux ((y*y) mod m) m (k-1)) in
                aux y n t


let rec isPrime n =
    if n == 1 then false
    else
            let (u, t) = power_two_decomp(n-1) in
            let rec g k =
                    (if k == 0 then true
                    else (mr_round n t u) && g (k-1)) in
            g 50

