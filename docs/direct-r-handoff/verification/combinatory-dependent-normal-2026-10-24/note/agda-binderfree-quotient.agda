Quotient : Ty → Set
Quotient A = Tm A Q./ WeakConversion

normalizeQ : Quotient A → Nf A
normalizeQ = Q.rec normal-isSet nf (λ _ _ → conversion-coherent)

quoteQ : Nf A → Quotient A
quoteQ n = Q.[ erase n ]

normalize-quote : (n : Nf A) → normalizeQ (quoteQ n) ≡ n
normalize-quote = nf-erase

quote-normalize : (q : Quotient A) → quoteQ (normalizeQ q) ≡ q
quote-normalize = Q.elimProp (λ q → Q.squash/ _ _)
  (λ t → sym (Q.eq/ t (erase (nf t)) (steps-conversion (nf-sound t))))

quotient-normal-iso : Iso (Quotient A) (Nf A)
quotient-normal-iso = iso normalizeQ quoteQ normalize-quote quote-normalize
