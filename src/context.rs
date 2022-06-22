use z3::{Config, Context};
use std::{sync::Mutex};
use once_cell::sync::Lazy;

static CTX: Lazy<Mutex<Context>> = Lazy::new(|| {
    let config = Config::new();
    let context = Context::new(&config);
    Mutex::new(context)
});

pub fn global_context() -> &'static Context {
    &CTX.lock().unwrap()
}