pub trait Lower {
    type Context;
    type Target;

    fn lower(&self, ctx: Self::Context) -> Self::Target;
}

pub trait Raise {
    type Context;
    type Target;

    fn raise(&self, ctx: Self::Context) -> Self::Target;
}
