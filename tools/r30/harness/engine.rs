// Filled in by tools/r30/engine_rust.py: the certified roots of Engine.lex.tex and Hypotheses.lex.tex on stdin.
use std::io::{self, BufRead, Write};

fn main() {
    let worker = std::thread::Builder::new().stack_size(1 << 30).spawn(serve).expect("thread");
    worker.join().expect("the harness thread");
}

fn serve() {
    let stdin = io::stdin();
    let mut out = io::BufWriter::new(io::stdout());
    for line in stdin.lock().lines() {
        let line = line.expect("stdin");
        let words: Vec<&str> = line.split_whitespace().collect();
        if words.is_empty() { continue; }
        let answer = match words[0] {
            "learn" => learn(&words[1..]),
            "schedule" => schedule(&words[1..]),
            "mint" => mint(&words[1..]),
            other => format!("error unknown request {}", other),
        };
        writeln!(out, "{}", answer).expect("stdout");
    }
}

fn learn(w: &[&str]) -> String {
    let (nw, no) = (w[0].parse::<usize>().unwrap(), w[1].parse::<usize>().unwrap());
    let mut table = @LA@::List::nil();
    for i in (0..nw).rev() {
        let k = 2 + 3 * i;
        table = @LA@::List::cons(@LA@::@LW@::C0(@LA@::Str::lit(w[k]), @LA@::Str::lit(w[k + 1]), w[k + 2].parse().unwrap()), table);
    }
    let mut outcomes = @LA@::List::nil();
    for i in (0..no).rev() {
        let k = 2 + 3 * nw + 3 * i;
        outcomes = @LA@::List::cons(@LA@::@LO@::C0(@LA@::Str::lit(w[k]), @LA@::Str::lit(w[k + 1]), w[k + 2] == "1"), outcomes);
    }
    let r = @LA@::run(table, outcomes);
    let mut cur = @LEARNED@;
    let mut rows = Vec::new();
    while let Some((h, t)) = cur.uncons() {
        let @LA@::@LW@::C0(s, f, v) = h;
        rows.push(format!("{} {} {}", s.text(), f.text(), v));
        cur = t;
    }
    rows.join(" ")
}

fn schedule(w: &[&str]) -> String {
    let (nw, family, na) = (w[0].parse::<usize>().unwrap(), w[1], w[2].parse::<usize>().unwrap());
    let mut table = @SC@::List::nil();
    for i in (0..nw).rev() {
        let k = 3 + 3 * i;
        table = @SC@::List::cons(@SC@::@SW@::C0(@SC@::Str::lit(w[k]), @SC@::Str::lit(w[k + 1]), w[k + 2].parse().unwrap()), table);
    }
    let mut apps = @SC@::List::nil();
    for i in (0..na).rev() { apps = @SC@::List::cons(@SC@::Str::lit(w[3 + 3 * nw + i]), apps); }
    let r = @SC@::run(table, @SC@::Str::lit(family), apps);
    let mut cur = @SCHEDULED@;
    let mut ids = Vec::new();
    while let Some((h, t)) = cur.uncons() { ids.push(h.text().to_string()); cur = t; }
    ids.join(" ")
}

fn bytes(word: &str) -> @MI@::Bytes {
    let octets: Vec<u8> = (1..word.len()).step_by(2).map(|i| u8::from_str_radix(&word[i..i + 2], 16).expect("hex")).collect();
    @MI@::Bytes::lit(&octets)
}

fn hex(b: &@MI@::Bytes) -> String {
    let mut s = String::from("x");
    for o in b.octets() { s.push_str(&format!("{:02x}", o)); }
    s
}

fn list<T: Clone>(xs: Vec<T>) -> @MI@::List<T> {
    xs.into_iter().rev().fold(@MI@::List::nil(), |l, x| @MI@::List::cons(x, l))
}

fn mint(w: &[&str]) -> String {
    let n: Vec<usize> = w[..5].iter().map(|x| x.parse().unwrap()).collect();
    let mut i = 5;
    let mut attempts = Vec::new();
    for _ in 0..n[0] { attempts.push(@MI@::@AT@::C0(bytes(w[i]), bytes(w[i + 1]), bytes(w[i + 2]))); i += 3; }
    let mut claims = Vec::new();
    for _ in 0..n[1] { claims.push(@MI@::@CL@::C0(bytes(w[i]), bytes(w[i + 1]), bytes(w[i + 2]))); i += 3; }
    let mut rows = Vec::new();
    for _ in 0..n[2] {
        let count: usize = w[i + 2].parse().unwrap();
        rows.push(@MI@::@RO@::C0(bytes(w[i]), bytes(w[i + 1]), list(w[i + 3..i + 3 + count].iter().map(|x| bytes(x)).collect())));
        i += 3 + count;
    }
    let store = list(w[i..i + n[3]].iter().map(|x| bytes(x)).collect());
    let mut cur = match @MI@::run(list(attempts), list(claims), list(rows), store, n[4] as u64, @MI@::List::nil()) {
        Ok(v) => v,
        Err(_) => return "violation overflow".to_string(),
    };
    let mut out = Vec::new();
    let mut count = 0;
    while let Some((h, t)) = cur.uncons() {
        let @MI@::@RET@::C0(_, form, label, weight, mut sources) = h;
        let mut names = Vec::new();
        while let Some((s, more)) = sources.uncons() { names.push(hex(&s)); sources = more; }
        out.push(format!("{} {} {} {} {}", hex(&label), hex(&form), weight, names.len(), names.join(" ")));
        count += 1;
        cur = t;
    }
    format!("{} {}", count, out.join(" "))
}
