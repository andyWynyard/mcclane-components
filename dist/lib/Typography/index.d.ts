import React from 'react';
import { LinkProps } from 'react-router-dom';
import { StyledSystemProps } from '../GenericComponent';
declare type AnchorProps = StyledSystemProps & Pick<LinkProps, 'to'> & {
    onClick?: (event: React.MouseEvent<HTMLAnchorElement>) => void;
};
export declare type Extra = StyledSystemProps & {
    children: string;
};
interface TypographyComponentProps {
    H1: React.FC<StyledSystemProps>;
    H2: React.FC<StyledSystemProps>;
    H3: React.FC<StyledSystemProps>;
    H4: React.FC<StyledSystemProps>;
    H5: React.FC<StyledSystemProps>;
    LargeLead: React.FC<StyledSystemProps>;
    SmallLead: React.FC<StyledSystemProps>;
    Paragraph: React.FC<StyledSystemProps>;
    SmallParagraph: React.FC<StyledSystemProps>;
    Link: React.FC<AnchorProps>;
}
declare const Typography: TypographyComponentProps;
export default Typography;
