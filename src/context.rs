use z3::{Config, Context};
use std::{sync::Mutex};
use once_cell::sync::Lazy;

struct Conf(Config);

struct Ctx(Context);

unsafe impl Sync for Ctx {}
unsafe impl Send for Ctx {}

static CTX: Lazy<Ctx> = Lazy::new(|| {
    let config = Config::new();
    let context = Context::new(&config);
    Ctx(context)
});

pub fn global_context() -> &'static Context {
    &CTX.0
}