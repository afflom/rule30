// Filled in by tools/r30/discover_rust.py: the certified roots of Discovery.lex.tex on stdin.
use std::io::{self, BufRead, Write};

fn nats<L>(xs: &[u64], nil: fn() -> L, cons: fn(u64, L) -> L) -> L {
    let mut out = nil();
    for x in xs.iter().rev() { out = cons(*x, out); }
    out
}

fn main() {
    // the roots recurse structurally over input-sized lists: run them on a large stack
    let worker = std::thread::Builder::new().stack_size(1 << 30).spawn(serve).expect("thread");
    worker.join().expect("the harness thread");
}

fn serve() {
    let stdin = io::stdin();
    let mut out = io::BufWriter::new(io::stdout());
    for line in stdin.lock().lines() {
        let line = line.expect("stdin");
        let mut it = line.split_whitespace();
        let kind = match it.next() { Some(k) => k.to_string(), None => continue };
        let nums: Vec<u64> = it.map(|x| x.parse().expect("a natural")).collect();
        let answer = match kind.as_str() {
            "columns" => columns(&nums),
            "relations" => relations(&nums),
            "recurrence" => recurrence(&nums),
            other => format!("error unknown request {}", other),
        };
        writeln!(out, "{}", answer).expect("stdout");
    }
}

fn words_c(xs: &[u64]) -> @C@::List<u64> { nats(xs, @C@::List::nil, @C@::List::cons) }
fn words_r(xs: &[u64]) -> @R@::List<u64> { nats(xs, @R@::List::nil, @R@::List::cons) }
fn unlist_c<T: Clone>(l: &@C@::List<T>) -> Vec<T> {
    let mut out = Vec::new();
    let mut cur = l.clone();
    while let Some((h, t)) = cur.uncons() { out.push(h); cur = t; }
    out
}
fn unlist_r<T: Clone>(l: &@R@::List<T>) -> Vec<T> {
    let mut out = Vec::new();
    let mut cur = l.clone();
    while let Some((h, t)) = cur.uncons() { out.push(h); cur = t; }
    out
}
fn unlist_q<T: Clone>(l: &@Q@::List<T>) -> Vec<T> {
    let mut out = Vec::new();
    let mut cur = l.clone();
    while let Some((h, t)) = cur.uncons() { out.push(h); cur = t; }
    out
}

fn columns(n: &[u64]) -> String {
    let (width, nb, ns) = (n[0], n[1] as usize, n[2] as usize);
    let per = (n.len() - 3 - 3 * ns) / nb;
    let mut bases = @C@::List::nil();
    for i in (0..nb).rev() { bases = @C@::List::cons(words_c(&n[3 + i * per..3 + (i + 1) * per]), bases); }
    let off = 3 + nb * per;
    let mut specs = @C@::List::nil();
    for i in (0..ns).rev() {
        let s = &n[off + 3 * i..off + 3 * i + 3];
        specs = @C@::List::cons((s[0], (s[1], s[2])), specs);
    }
    match @C@::run(width, bases, specs) {
        Ok(cols) => unlist_c(&cols).iter().map(|w| unlist_c(w).iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")).collect::<Vec<_>>().join(" "),
        Err(_) => "violation overflow".to_string(),
    }
}

fn relations(n: &[u64]) -> String {
    let (width, m) = (n[0], n[1] as usize);
    let per = (n.len() - 2) / m;
    let mut cols = @R@::List::nil();
    for i in (0..m).rev() { cols = @R@::List::cons(words_r(&n[2 + i * per..2 + (i + 1) * per]), cols); }
    match @R@::run((width, cols)) {
        Ok(Ok(rels)) => unlist_r(&rels).iter().map(|m| unlist_r(m).iter().map(|b| if *b { '1' } else { '0' }).collect::<String>()).collect::<Vec<_>>().join(" "),
        Ok(Err((a, b))) => format!("violation {}{}", a as u8, b as u8),
        Err(_) => "violation overflow".to_string(),
    }
}

fn recurrence(n: &[u64]) -> String {
    let k = n[0] as usize;
    let mut bits = @Q@::List::nil();
    for i in (0..k).rev() { bits = @Q@::List::cons(n[1 + i] == 1, bits); }
    match @Q@::run(bits) {
        Ok(Ok(c)) => unlist_q(&c).iter().map(|b| if *b { '1' } else { '0' }).collect::<String>(),
        Ok(Err((a, b))) => format!("violation {}{}", a as u8, b as u8),
        Err(_) => "violation overflow".to_string(),
    }
}
