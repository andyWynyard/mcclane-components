import React from 'react';
import { SpaceProps, TypographyProps, LayoutProps, FlexboxProps, GridProps, BackgroundProps, BorderProps, PositionProps, ShadowProps } from 'styled-system';
export declare type StyledSystemProps = SpaceProps & TypographyProps & LayoutProps & FlexboxProps & GridProps & BackgroundProps & BorderProps & PositionProps & ShadowProps & {
    color?: string;
    as?: keyof JSX.IntrinsicElements | React.ComponentType<any>;
};
declare const _default: import("styled-components").StyledComponent<"div", any, {}, never>;
export default _default;
